module

-- separate module: the windowed exponentiation, the largest of the CRT's proofs, apart from `CrtR2`, which `recombineP`'s proof imports too
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontSqr
public import VerifiedGarbage.Proof.Bignum.RISCV64.Pow57
public import VerifiedGarbage.Proof.Bignum.RISCV64.WinSelect
public import VerifiedGarbage.Impl.Bignum.RISCV64.ModExp
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontRounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Modular exponentiation by four-bit windows on RISC-V

`powWin_ok`: `ModExp.powWin`, in a working space of 24 arrays (`WCtx`), as on
PPC64LE (`Proof/Bignum/PPC64LE/{WinBase,WinTable,WinSel,WinPow}.lean`): the
table `T_j = x^j R mod m` (`table_ok`), the masked scan of the whole table
(`select_ok`), a window of four squares (`sqrTail`) and a multiplication
(`window_ok`), a byte's two windows (`byteWin_ok`), and the power
`x^d mod m` in array 4. `powWin57_ok`: the same for `powWin57`, in radix
`2⁵⁷`, and `powWinCall_ok` the function, which chooses between the two.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Win

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.ModExp
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot slot_sep Arrays)
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)

/-- Array `j`'s number. -/
abbrev A (m : Mem) (B : Addr) (w j : Nat) : Nat := wordsVal m B (slot w j) w

/-- The mask of `b`: all ones if `b`, else 0. -/
abbrev mask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem slot_lt {w j k : Nat} (h : j < k) : slot w j + 8 * (w + 2) ≤ slot w k := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ k by omega_arith)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega_arith

/-- Arrays 1 to 23: everything `powWin` may write. -/
abbrev WinO (B : Addr) (w : Nat) (m m' : Mem) : Prop := Outside B (slot w 1) (23 * (8 * (w + 2))) m m'

/-- What the Montgomery multiplications need, with `N` the modulus in array
0. -/
structure WCtx (s : State) (B : Addr) (Z w N : Nat) : Prop where
  scr : Scr s B Z
  w2 : 2 ≤ w
  w31 : w < 2 ^ 31
  hZ : slot w 24 ≤ Z
  a7 : s.gpr .a7 = off B (slot w 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 w
  inv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  n : A s.mem B w 0 = N

/-- The registers `WCtx` reads. -/
def ctxRegs : List Reg := [.a7, .s5, .t0, .t1]

theorem WCtx.sl {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {j : Nat} (hj : j < 24) :
    slot w j + 8 * (w + 2) ≤ Z :=
  Nat.le_trans (slot_lt hj) h.hZ

theorem WCtx.nw {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) : B.toNat + slot w 24 ≤ 2 ^ 64 := by
  have := h.scr.nowrap; have := h.hZ; omega_arith

theorem slot24 (w : Nat) : slot w 24 = slot w 1 + 23 * (8 * (w + 2)) := by unfold slot; omega_arith

theorem slot_win {w o : Nat} (h1 : 1 ≤ o) (h24 : o < 24) :
    slot w 1 ≤ slot w o ∧ slot w o + 8 * (w + 2) ≤ slot w 1 + 23 * (8 * (w + 2)) := by
  have := slot_lt (w := w) h24
  obtain e24 := slot24 w
  refine ⟨?_, by omega_arith⟩
  unfold slot; have := Nat.mul_le_mul_right (8 * (w + 2)) h1; omega_arith

/-- An array apart from the arrays that changed. -/
theorem arr_eq {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') {j : Nat}
    (hj : j < 24) (hjs : ∀ k ∈ js, k ≠ j) (hn : B.toNat + slot w 24 ≤ 2 ^ 64) : A m' B w j = A m B w j := by
  have := slot_lt (w := w) hj
  exact Pub.arrays_V h hjs (by omega_arith)

/-- One array changed: the frame of `Arrays`. -/
theorem arr1 {B : Addr} {w o : Nat} {n : Nat} {m m' : Mem} (h : Outside B (slot w o) n m m')
    (hn : n ≤ 8 * (w + 2)) : Arrays B w [o] m m' :=
  Arrays.of_outside (by simp) h (Nat.le_refl _) (by omega_arith)

theorem win_of_arrays {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hjs : ∀ j ∈ js, 1 ≤ j ∧ j < 24) : WinO B w m m' := fun x hx => h x fun j hj => by
  have := slot_win (w := w) (hjs j hj).1 (hjs j hj).2
  simp only [VG.Proof.Bignum.ofs] at hx ⊢
  omega_arith

theorem WinO.trans {B : Addr} {w : Nat} {m₁ m₂ m₃ : Mem} (a : WinO B w m₁ m₂) (b : WinO B w m₂ m₃) :
    WinO B w m₁ m₃ := Outside.trans a b

/-- The context after code that writes only arrays 1–23 and none of
`ctxRegs`. -/
theorem WCtx.of {s t : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ ctxRegs, r ∉ rs) (o : WinO B w s.mem t.mem) : WCtx t B Z w N := by
  have hn := h.nw
  obtain s0 := slot_lt (w := w) (show 0 < 24 by decide)
  obtain e1 : slot w 1 = slot w 0 + 8 * (w + 2) := by unfold slot; omega_arith
  obtain g := fun r hr => k.gpr (r := r) (hrs r hr)
  refine ⟨h.scr.congr k.2.2, h.w2, h.w31, h.hZ, (g .a7 (by decide)).trans h.a7,
    (g .s5 (by decide)).trans h.s5, (g .t0 (by decide)).trans h.t0, ?_, ?_⟩
  · have hw0 : Mont.word t.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
      Outside.word o (Or.inl (by omega_using [e1, s0])) (by omega_using [hn, s0])
    rw [g .t1 (by decide), hw0]
    exact h.inv
  · rw [← h.n]
    exact Outside.wordsVal o (Or.inl (by omega_arith)) (by omega_arith)

theorem WCtx.regs {s t : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ ctxRegs, r ∉ rs) (hm : t.mem = s.mem) : WCtx t B Z w N :=
  h.of k hrs (by rw [hm]; exact Outside.refl _ _ _ _)

/-- A Montgomery multiplication in the context. -/
theorem WCtx.mont {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {o a b : Nat} (ho : o < 24) (ha : a < 24)
    (hb : b < 24) (ho1 : o ≠ 0) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2) (hB : A s.mem B w b < N) :
    WP isa (montOp o a b) s fun t =>
      (WCtx t B Z w N ∧ A t.mem B w o < N ∧
        A t.mem B w o * 2 ^ (64 * w) % N = A s.mem B w a * A s.mem B w b % N ∧
        (∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ o → A t.mem B w j = A s.mem B w j) ∧
        WinO B w s.mem t.mem) ∧ Keep Pub.montRegs s t := by
  refine WP.mono (Pub.montOpN_ok h.scr (n := 24) (by decide) ho ha hb ho2 ho3 ha2 hb2 h.w2 h.w31 h.hZ h.a7 h.s5
    h.t0 h.inv (by rw [show wordsVal s.mem B (slot w 0) w = N from h.n]; exact hB))
    fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  obtain op := win_of_arrays out (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega_arith)
  rw [show wordsVal s.mem B (slot w 0) w = N from h.n] at hlt he
  exact ⟨⟨h.of k (by decide) op, hlt, he, fun j hj h2 h3 hjo => arr_eq out hj (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith) h.nw, op⟩, k⟩

/-- The registers a square writes. -/
def sqRegs : List Reg := [.a2, .a3, .a5, .a6] ++ sqrRegs

/-- A square (`sqrOp o a p`) in the context, the temporary `p`. -/
theorem WCtx.sqr {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {o a p : Nat} (ho : o < 24)
    (ha : a < 24) (hp : p < 24) (ho1 : o ≠ 0) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (ha3 : a ≠ 3)
    (hp0 : p ≠ 0) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpo : p ≠ o) (hA : A s.mem B w a < N) :
    WP isa (sqrOp o a p) s fun t =>
      (WCtx t B Z w N ∧ A t.mem B w o < N ∧
        A t.mem B w o * 2 ^ (64 * w) % N = A s.mem B w a * A s.mem B w a % N ∧
        (∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ p → j ≠ o → A t.mem B w j = A s.mem B w j) ∧
        WinO B w s.mem t.mem) ∧ Keep sqRegs s t := by
  unfold sqrOp
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) h.a7 h.s5 o) fun t₁ ⟨⟨a2, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a3) (by decide) ((k1.gpr (by decide)).trans h.a7)
    ((k1.gpr (by decide)).trans h.s5) a) fun t₂ ⟨⟨a3, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k12.gpr (by decide)).trans h.a7)
    ((k12.gpr (by decide)).trans h.s5) 2) fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  obtain k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k13.gpr (by decide)).trans h.a7)
    ((k13.gpr (by decide)).trans h.s5) p) fun t₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  obtain k14 := k13.trans k4
  obtain hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  obtain c4 := h.regs k14 (by decide) hm
  obtain g2 : t₄.gpr .a2 = off B (slot w o) := by rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), a2]
  obtain g3 : t₄.gpr .a3 = off B (slot w a) := by rw [k4.gpr (by decide), k3.gpr (by decide), a3]
  obtain g5 : t₄.gpr .a5 = off B (slot w 2) := by rw [k4.gpr (by decide), a5]
  rw [← hm] at hA ⊢
  refine WP.mono (sqrTailN_ok c4.scr (n := 24) (by decide) ho ha hp ho2 ho3 ha2 ha3 hp0 hp2 hp3 hpo c4.w2 c4.w31
    c4.hZ g2 g3 g5 a6 c4.a7 c4.t0 c4.inv (by rw [show wordsVal t₄.mem B (slot w 0) w = N from c4.n]; exact hA))
    fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  obtain op := win_of_arrays out (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega_arith)
  rw [show wordsVal t₄.mem B (slot w 0) w = N from c4.n] at hlt he
  exact ⟨⟨c4.of k (by decide) op, hlt, he, fun j hj h2 h3 hjp hjo => arr_eq out hj (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith) c4.nw, op⟩, (k14.trans k).mono (by decide)⟩

/-! ## Copies and selections -/

/-- `selectAcc64` with the bases already in `a2`, `a5` and `a6`. -/
theorem selectAt_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {b : Bool} {o a t : Nat}
    (ho : o < 24) (ha : a < 24) (ht : t < 24) (hoa : o ≠ a) (hot : o ≠ t)
    (h2 : s.gpr .a2 = off B (slot w o)) (h5 : s.gpr .a5 = off B (slot w a)) (h6 : s.gpr .a6 = off B (slot w t))
    (h4 : s.gpr .s4 = mask b) :
    WP isa selectAcc64 s fun s' =>
      (A s'.mem B w o = (if b then A s.mem B w a else A s.mem B w t) ∧
        Outside B (slot w o) (8 * w) s.mem s'.mem) ∧ Keep [.a0, .t3, .t4, .t5, .s2, .s3] s s' := by
  obtain sep := fun {j k : Nat} (hjk : j ≠ k) => slot_sep (w := w) hjk
  obtain hO := h.sl ho
  obtain hA := h.sl ha
  obtain hT := h.sl ht
  obtain al := slot_al w
  exact WP.mono (selectAcc64_ok h.scr (dA := slot w a) (dT := slot w t) (dO := slot w o) (w := w) (b := b)
      h5 h6 h2 h.t0 h4 (by have := h.w2; omega_arith) h.w31 (al a) (al t) (al o)
      (by omega_arith) (by omega_arith) (by omega_arith)
      (by have := sep hoa; omega_arith) (by have := sep hot; omega_arith)) fun s' ⟨hv, hout, k⟩ =>
    ⟨⟨hv, hout⟩, k⟩

theorem exec_li_m1 {s : State} {d : Reg} : exec (.li d (-1)) s = some (s.write d (BitVec.allOnes 64)) := by
  rw [exec_li (by decide)]; rfl

theorem ones_ok (s : State) :
    WP isa (.block ones) s fun t => (t.gpr .s4 = mask true ∧ t.mem = s.mem) ∧ Keep [.s4] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold ones
  brun [exec_li_m1]
  rfl

/-- The registers `copy` and `toEntry` write. -/
def copyRegs : List Reg := [.a0, .t2, .t3, .t4, .t5, .s2, .s3, .s4, .a2, .a5, .a6]

/-- `copy o a`: array `o` := array `a`. -/
theorem copy_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {o a : Nat} (ho : o < 24) (ha : a < 24)
    (hoa : o ≠ a) :
    WP isa (copy o a) s fun t =>
      (A t.mem B w o = A s.mem B w a ∧ Outside B (slot w o) (8 * w) s.mem t.mem) ∧ Keep copyRegs s t := by
  unfold copy
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ones_ok s) fun t₁ ⟨⟨h4, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k1.gpr (by decide)).trans h.a7)
    ((k1.gpr (by decide)).trans h.s5) a) fun t₂ ⟨⟨a5, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k12.gpr (by decide)).trans h.a7)
    ((k12.gpr (by decide)).trans h.s5) a) fun t₃ ⟨⟨a6, m3⟩, k3⟩ => ?_
  obtain k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k13.gpr (by decide)).trans h.a7)
    ((k13.gpr (by decide)).trans h.s5) o) fun t₄ ⟨⟨a2, m4⟩, k4⟩ => ?_
  obtain k14 := k13.trans k4
  obtain hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (selectAt_ok (h.regs k14 (by decide) hm) (b := true) ho ha ha hoa hoa a2
    (by rw [k4.gpr (by decide), k3.gpr (by decide), a5]) (by rw [k4.gpr (by decide), a6])
    (by rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), h4]))
    fun t ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  exact ⟨⟨by simpa only [ite_true] using hv, hout⟩, (k14.trans k).mono (by decide)⟩

theorem entry_addr (B : Addr) (w j : Nat) :
    (BitVec.ofNat 64 j + BitVec.ofNat 64 8) * BitVec.ofNat 64 (8 * (w + 2)) + off B (slot w 0) =
      off B (slot w (8 + j)) := by
  simp only [off, slot, Impl.Bignum.hdrBytes, Nat.zero_mul, Nat.add_zero]
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul, Nat.add_comm 8 j, BitVec.ofNat_add 256]
  ac_rfl

/-- `entry rd rj`: the base of table entry `j` (in `rj`) into `rd`. -/
theorem entry_ok {s : State} {B : Addr} {Z w N j : Nat} (h : WCtx s B Z w N) {rd rj : Reg}
    (hd : rd = .a2 ∧ rj = .s7 ∨ rd = .a5 ∧ rj = .s8) (hj : s.gpr rj = BitVec.ofNat 64 j) :
    WP isa (.block (entry rd rj)) s fun t =>
      (t.gpr rd = off B (slot w (8 + j)) ∧ t.mem = s.mem) ∧ Keep [.t2, rd] s t := by
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold entry
    brun [hj, h.s5, h.a7, entry_addr]

/-- `toEntry`: table entry `j` (in `s7`) := array 6. -/
theorem toEntry_ok {s : State} {B : Addr} {Z w N j : Nat} (h : WCtx s B Z w N)
    (h7 : s.gpr .s7 = BitVec.ofNat 64 j) (hj : j < 16) :
    WP isa toEntry s fun t =>
      (A t.mem B w (8 + j) = A s.mem B w 6 ∧ Outside B (slot w (8 + j)) (8 * w) s.mem t.mem) ∧
        Keep copyRegs s t := by
  unfold toEntry
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ones_ok s) fun t₁ ⟨⟨h4, m1⟩, k1⟩ => ?_
  obtain c1 := h.regs k1 (by decide) m1
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok (j := j) c1 (.inl ⟨rfl, rfl⟩) (by rw [k1.gpr (by decide), h7]))
    fun t₂ ⟨⟨a2, m2⟩, k2⟩ => ?_
  obtain c2 := c1.regs k2 (by decide) m2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) c2.a7 c2.s5 6) fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  obtain c3 := c2.regs k3 (by decide) m3
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) c3.a7 c3.s5 6) fun t₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  obtain c4 := c3.regs k4 (by decide) m4
  obtain k14 := ((k1.trans k2).trans k3).trans k4
  obtain hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (selectAt_ok c4 (b := true) (o := 8 + j) (a := 6) (t := 6) (by omega_arith) (by decide)
    (by decide) (by omega_arith) (by omega_arith) (by rw [k4.gpr (by decide), k3.gpr (by decide), a2])
    (by rw [k4.gpr (by decide), a5]) a6
    (by rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), h4])) fun t ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  exact ⟨⟨by simpa only [ite_true] using hv, hout⟩, (k14.trans k).mono (by decide)⟩

/-- A Montgomery product of powers of `x` in Montgomery form. -/
theorem mont_pow {o a b X i j R N : Nat} (hR : Nat.Coprime R N) (ha : a % N = X ^ i * R % N)
    (hb : b % N = X ^ j * R % N) (h : o * R % N = a * b % N) : o % N = X ^ (i + j) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [h, Nat.mul_mod, ha, hb, ← Nat.mul_mod, Nat.pow_add]
  congr 1
  ac_rfl

/-- The table's entries below `j`, if `R² mod m` is right. -/
def TabUpTo (m : Mem) (B : Addr) (w N X RR j : Nat) : Prop :=
  ∀ i < j, A m B w (8 + i) < N ∧ (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N →
    A m B w (8 + i) % N = X ^ i * 2 ^ (64 * w) % N)

/-- The registers the table writes. -/
def tabRegs : List Reg := Pub.montRegs ++ copyRegs ++ [.s0, .t3, .t5, .s7, .t2]

theorem arrO {B : Addr} {w o : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * w) m m') (h1 : 1 ≤ o)
    (h24 : o < 24) : WinO B w m m' :=
  win_of_arrays (arr1 h (by omega_arith)) (by simp; omega_arith)

theorem arr_out {B : Addr} {w o j : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * w) m m')
    (hj : j < 24) (hne : j ≠ o) (hn : B.toNat + slot w 24 ≤ 2 ^ 64) : A m' B w j = A m B w j :=
  arr_eq (arr1 h (by omega_arith)) hj (by simp; omega_arith) hn

/-- `table`. -/
theorem table_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hN : 2 ≤ N) (hodd : N % 2 = 1)
    (hRR : A s.mem B w 1 < N) :
    WP isa table s fun t =>
      (WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧ A t.mem B w 1 = A s.mem B w 1 ∧
        A t.mem B w 4 = A s.mem B w 4 ∧ A t.mem B w 7 = 1 ∧ A t.mem B w 6 = A t.mem B w 8 ∧
        TabUpTo t.mem B w N (A s.mem B w 4) (A s.mem B w 1) 16) ∧ Keep tabRegs s t := by
  have hn := h.nw
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hX : A s.mem B w 4 = X
  generalize hRRd : A s.mem B w 1 = RR at hRR
  unfold table
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok h.scr (by have := h.w2; omega_arith) h.w31
    (Nat.le_trans (by unfold slot; omega_arith) h.hZ) h.a7 h.s5 h.t0) fun s₁ ⟨⟨h7, o1⟩, k1⟩ => ?_)
  replace h7 : A s₁.mem B w 7 = 1 := h7
  obtain c1 := h.of k1 (by decide) (arrO o1 (by decide) (by decide))
  obtain R1 : A s₁.mem B w 1 = RR := by rw [arr_out o1 (by decide) (by decide) hn, hRRd]
  obtain X1 : A s₁.mem B w 4 = X := by rw [arr_out o1 (by decide) (by decide) hn, hX]
  -- `T_0 = R mod m`.
  refine WP.seq (WP.mono (c1.mont (o := 8) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h7]; omega_arith)) fun s₂ ⟨⟨c2, lt2, e2, v2, o2⟩, k2⟩ => ?_)
  rw [h7, Nat.mul_one, R1] at e2
  obtain T0 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₂.mem B w 8 % N = X ^ 0 * 2 ^ (64 * w) % N :=
    fun hE => by
      rw [Nat.pow_zero, Nat.one_mul]
      exact VG.Proof.Bignum.mont_cancel hR (by rw [e2, hE, Nat.mod_mod])
  obtain R2 : A s₂.mem B w 1 = RR := by rw [v2 1 (by decide) (by decide) (by decide) (by decide), R1]
  obtain X2 : A s₂.mem B w 4 = X := by rw [v2 4 (by decide) (by decide) (by decide) (by decide), X1]
  obtain S2 : A s₂.mem B w 7 = 1 := by rw [v2 7 (by decide) (by decide) (by decide) (by decide), h7]
  -- `T_1 = x R mod m`.
  refine WP.seq (WP.mono (c2.mont (o := 9) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R2]; exact hRR))
    fun s₃ ⟨⟨c3, lt3, e3, v3, o3⟩, k3⟩ => ?_)
  rw [X2, R2] at e3
  obtain T1 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₃.mem B w 9 % N = X ^ 1 * 2 ^ (64 * w) % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [e3, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_one, Nat.mul_assoc]
  obtain R3 : A s₃.mem B w 1 = RR := by rw [v3 1 (by decide) (by decide) (by decide) (by decide), R2]
  obtain X3 : A s₃.mem B w 4 = X := by rw [v3 4 (by decide) (by decide) (by decide) (by decide), X2]
  obtain S3 : A s₃.mem B w 7 = 1 := by rw [v3 7 (by decide) (by decide) (by decide) (by decide), S2]
  obtain E3 : A s₃.mem B w 8 = A s₂.mem B w 8 := v3 8 (by decide) (by decide) (by decide) (by decide)
  -- `a := T_1`.
  refine WP.seq (WP.mono (copy_ok c3 (o := 6) (a := 9) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨a4, o4⟩, k4⟩ => ?_)
  obtain c4 := c3.of k4 (by decide) (arrO o4 (by decide) (by decide))
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = BitVec.ofNat 64 2 ∧ t.mem = s₄.mem)
    (by brun [Pub.pub_li1, exec_li]) (by rfl) (by rfl)) fun s₅ ⟨⟨a7, m5⟩, k5⟩ => ?_)
  obtain c5 := c4.regs k5 (by decide) m5
  obtain O5 : WinO B w s.mem s₅.mem := by
    rw [m5]
    exact (((arrO o1 (by decide) (by decide)).trans o2).trans o3).trans (arrO o4 (by decide) (by decide))
  obtain K : ∀ j, j < 24 → j ≠ 6 → A s₅.mem B w j = A s₃.mem B w j := fun j hj h6 => by
    rw [m5]; exact arr_out o4 hj h6 hn
  obtain tab2 : TabUpTo s₅.mem B w N X RR 2 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl
    · rw [K 8 (by decide) (by decide), E3]; exact ⟨lt2, T0⟩
    · rw [K 9 (by decide) (by decide)]; exact ⟨lt3, T1⟩
  obtain a5 : A s₅.mem B w 6 = A s₃.mem B w 9 := by rw [m5, a4]
  -- The loop: entries 2 to 15.
  refine WP.seq (WP.mono (count_loop (n := 14) (cr := .t2) (by decide)
      (fun k t => WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧ t.gpr .s7 = BitVec.ofNat 64 (2 + k) ∧
        A t.mem B w 1 = RR ∧ A t.mem B w 4 = X ∧ A t.mem B w 7 = 1 ∧ A t.mem B w 9 = A s₃.mem B w 9 ∧
        TabUpTo t.mem B w N X RR (2 + k) ∧ A t.mem B w 6 < N ∧
        (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A t.mem B w 6 % N = X ^ (1 + k) * 2 ^ (64 * w) % N) ∧
        Keep tabRegs s t)
      (fun k hk t ⟨ct, ot, t7, t1, t4, t7', t9, ttab, t6l, t6, kt⟩ => ?_)
      ⟨c5, O5, a7, by rw [K 1 (by decide) (by decide), R3], by rw [K 4 (by decide) (by decide), X3],
        by rw [K 7 (by decide) (by decide), S3], K 9 (by decide) (by decide), tab2,
        by rw [a5]; exact lt3, fun hE => by rw [a5]; exact T1 hE,
        ((((k1.trans k2).trans k3).trans k4).trans k5).mono (by decide)⟩)
    fun t ⟨ct, ot, _, t1, t4, t7, _, ttab, _, _, kt⟩ => ?_)
  · refine WP.seq (WP.mono (ct.mont (o := 6) (a := 6) (b := 9) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [t9]; exact lt3))
      fun u ⟨⟨cu, lu, eu, vu, ou⟩, ku⟩ => ?_)
    refine WP.seq (WP.mono (toEntry_ok cu (j := 2 + k) (by rw [ku.gpr (by decide), t7]) (by omega_arith))
      fun x ⟨⟨xe, xo⟩, kx⟩ => ?_)
    obtain cx := cu.of kx (by decide) (arrO xo (by omega_arith) (by omega_arith))
    obtain hend : WP isa (.block [.addi .s7 .s7 1, .addi .t2 .s7 (-16)]) x fun y =>
        (y.gpr .s7 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 ∧
          y.gpr .t2 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 - BitVec.ofNat 64 16 ∧ y.mem = x.mem) ∧
          Keep [.s7, .t2] x y := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [(kx.gpr (r := .s7) (by decide)).trans ((ku.gpr (r := .s7) (by decide)).trans t7)]
    obtain M : ∀ j, j < 24 → j ≠ 2 → j ≠ 3 → j ≠ 6 → j ≠ 8 + (2 + k) → A x.mem B w j = A t.mem B w j :=
      fun j hj h2 h3 h6 he => by rw [arr_out xo hj he hn, vu j hj h2 h3 h6]
    obtain pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A u.mem B w 6 % N = X ^ (2 + k) * 2 ^ (64 * w) % N :=
      fun hE => by
        rw [mont_pow hR (t6 hE) (by rw [t9]; exact T1 hE) eu, show 1 + k + 1 = 2 + k by omega_arith]
    refine WP.mono hend fun y ⟨⟨y7, y2, ym⟩, ky⟩ =>
      ⟨⟨cx.regs ky (by decide) ym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [ym]; exact (ot.trans ou).trans (arrO xo (by omega_arith) (by omega_arith))
    · rw [y7, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [ym, M 1 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t1]
    · rw [ym, M 4 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t4]
    · rw [ym, M 7 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t7']
    · rw [ym, M 9 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t9]
    · intro i hi
      rw [ym]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < 2 + k + 1 by omega_arith) with hi | rfl
      · rw [M (8 + i) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
        exact ttab i hi
      · rw [xe]
        exact ⟨lu, pw⟩
    · rw [ym, arr_out xo (by decide) (by omega_arith) hn]; exact lu
    · intro hE
      rw [ym, arr_out xo (by decide) (by omega_arith) hn, pw hE, show 2 + k = 1 + (k + 1) by omega_arith]
    · exact (((kt.trans ku).trans kx).trans ky).mono (by decide)
    · rw [y2, ← BitVec.ofNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
  · -- `a := T_0`.
    refine WP.mono (copy_ok ct (o := 6) (a := 8) (by decide) (by decide) (by decide)) fun u ⟨⟨ua, uo⟩, ku⟩ =>
      ⟨⟨ct.of ku (by decide) (arrO uo (by decide) (by decide)),
        ot.trans (arrO uo (by decide) (by decide)), by rw [arr_out uo (by decide) (by decide) hn, t1],
        by rw [arr_out uo (by decide) (by decide) hn, t4], by rw [arr_out uo (by decide) (by decide) hn, t7],
        by rw [ua, arr_out uo (by decide) (by decide) hn], fun i hi => ?_⟩, (kt.trans ku).mono (by decide)⟩
    rw [arr_out uo (by omega_arith) (by omega_arith) hn]
    exact ttab i hi

/-! ## The selection of a table entry -/

theorem sub1_sign {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 (if x = 0 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  have : x = 0 ↔ x.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    this]
  split <;> omega_arith

/-- A bounded one-hot bit produces exactly one all-ones selection mask. -/
theorem wordSelect_mask : ∀ (d j : Fin 16),
    (0#64 : BitVec 64) - ((((1#64 : BitVec 64) <<< d.val) >>> j.val) &&& 1#64) =
      if j.val = d.val then BitVec.allOnes 64 else 0#64 := by decide

/-- One column word is read without changing memory or its public pointer. -/
theorem wordSelectCell_ok {s : State} {B : Addr} {Z w i j d : Nat} (hs : Scr s B Z)
    (hptr : s.gpr .s1 = off B (slot w (8 + j) + 8 * i))
    (hhot : s.gpr .t6 = ((1#64 : BitVec 64) <<< d) >>> j) (hzero : s.gpr .s3 = 0#64)
    (hj : j < 16) (hd : d < 16) (hi : i < w) (hZ : slot w 24 ≤ Z) :
    WP isa (.block wordSelectCell) s fun t =>
      (t.gpr .s0 = (if j = d then s.gpr .s0 ||| word s.mem B (slot w (8 + j) + 8 * i)
        else s.gpr .s0) ∧ t.mem = s.mem) ∧ Keep [.s2, .t2, .s0] s t := by
  obtain hslot := slot_lt (w := w) (show 8 + j < 24 by omega_arith)
  obtain hfit : slot w (8 + j) + 8 * i + 8 ≤ Z := by omega_arith
  obtain hal : (slot w (8 + j) + 8 * i) % 8 = 0 := by
    have := slot_al w (8 + j); omega_arith
  obtain hm : (0#64 : BitVec 64) - ((((1#64 : BitVec 64) <<< d) >>> j) &&& 1#64) =
      if j = d then BitVec.allOnes 64 else 0#64 := wordSelect_mask ⟨d, hd⟩ ⟨j, hj⟩
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold wordSelectCell
  brun [hptr, hhot, hzero, hs.ld hfit, hs.al8 hfit hal]
  rw [hm]
  by_cases he : j = d
  · simp only [he, ↓reduceIte, BitVec.and_allOnes, word]
  · simp only [he, ↓reduceIte, BitVec.and_zero, BitVec.or_zero]

/-- The public address of the next cell in one table column. -/
theorem wordSelect_next (w i j : Nat) :
    slot w (8 + j) + 8 * i + 8 * (w + 2) = slot w (8 + (j + 1)) + 8 * i := by
  unfold slot
  rw [show 8 + (j + 1) = (8 + j) + 1 by omega_arith]
  simp only [Nat.add_mul, Nat.one_mul]
  omega_arith

/-- The fixed prefix is extended by one cell and pointer advance. -/
theorem wordSelectPrefix_succ (n : Nat) : wordSelectPrefix (n + 1) =
    wordSelectPrefix n ++ (wordSelectCell ++ wordSelectAdvance) := by
  simp only [wordSelectPrefix, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- A read-only prefix of the column scan. The accumulator is zero until
its digit's entry, then keeps that entry's word. -/
theorem wordSelectPrefix_ok {s : State} {B : Addr} {Z w i d : Nat} (hs : Scr s B Z)
    (hptr : s.gpr .s1 = off B (slot w 8 + 8 * i))
    (hhot : s.gpr .t6 = (1#64 : BitVec 64) <<< d) (hacc : s.gpr .s0 = 0#64)
    (hzero : s.gpr .s3 = 0#64) (hstride : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (hd : d < 16) (hi : i < w) (hZ : slot w 24 ≤ Z) (n : Nat) (hn : n ≤ 15) :
    WP isa (.block (wordSelectPrefix n)) s fun t =>
      (t.gpr .s0 = (if d < n then word s.mem B (slot w (8 + d) + 8 * i) else 0#64) ∧
        t.gpr .s1 = off B (slot w (8 + n) + 8 * i) ∧
        t.gpr .t6 = ((1#64 : BitVec 64) <<< d) >>> n ∧ t.mem = s.mem) ∧
        Keep [.s0, .s1, .s2, .t2, .t6] s t := by
  induction n with
  | zero =>
    simp only [wordSelectPrefix, List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨⟨by simpa only [Nat.not_lt_zero, ↓reduceIte] using hacc,
      by simpa only [Nat.add_zero] using hptr, by simpa only [BitVec.ushiftRight_zero] using hhot, rfl⟩,
      Keep.refl _ _⟩
  | succ n ih =>
    rw [wordSelectPrefix_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t₁ ⟨⟨v1, p1, b1, m1⟩, k1⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (wordSelectCell_ok (hs.congr k1.2.2) p1 b1
      ((k1.gpr (by decide)).trans hzero) (by omega_arith) hd hi hZ)
      fun t₂ ⟨⟨v2, m2⟩, k2⟩ => ?_
    obtain value : t₂.gpr .s0 = if d < n + 1 then word s.mem B (slot w (8 + d) + 8 * i) else 0#64 := by
      rw [m1, v1] at v2
      by_cases he : n = d
      · simpa [he] using v2
      · have e : (d < n) = (d < n + 1) := propext (by omega_arith)
        simpa only [he, ↓reduceIte, e] using v2
    obtain k12 := k1.trans k2
    obtain hptr2 : t₂.gpr .s1 = off B (slot w (8 + n) + 8 * i) := (k2.gpr (by decide)).trans p1
    obtain hhot2 : t₂.gpr .t6 = ((1#64 : BitVec 64) <<< d) >>> n := (k2.gpr (by decide)).trans b1
    obtain hstride2 := (k12.gpr (r := .s5) (by decide)).trans hstride
    obtain advance : WP isa (.block wordSelectAdvance) t₂ fun t =>
        (t.gpr .s1 = off B (slot w (8 + (n + 1)) + 8 * i) ∧
          t.gpr .t6 = ((1#64 : BitVec 64) <<< d) >>> (n + 1) ∧ t.mem = t₂.mem) ∧
          Keep [.s1, .t6] t₂ t := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      unfold wordSelectAdvance
      brun [hptr2, hhot2, hstride2, off_add, wordSelect_next, ← BitVec.shiftRight_add]
    exact WP.mono advance fun t ⟨⟨p3, b3, m3⟩, k3⟩ =>
      ⟨⟨(k3.gpr (by decide)).trans value, p3, b3, m3.trans (m2.trans m1)⟩,
        (k12.trans k3).mono (by decide)⟩

/-- Start a column with public addresses and a secret digit held only in a
one-hot register. -/
theorem wordSelectHead_ok {s : State} {B : Addr} {w i d : Nat}
    (hptr : s.gpr .t3 = off B (slot w 8 + 8 * i))
    (h1 : s.gpr .a1 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa (.block wordSelectHead) s fun t =>
      (t.gpr .s1 = off B (slot w 8 + 8 * i) ∧ t.gpr .s0 = 0#64 ∧ t.gpr .s3 = 0#64 ∧
        t.gpr .t6 = (1#64 : BitVec 64) <<< d ∧ t.mem = s.mem) ∧ Keep [.s1, .s0, .s3, .t6] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold wordSelectHead
  brun [hptr, h1, Pub.pub_li0, Pub.pub_li1, exec_li, exec_sllReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show d < 64 by omega_arith)]

/-- All sixteen cells of one column select exactly its digit's word. -/
theorem wordSelectWord_ok {s : State} {B : Addr} {Z w i d : Nat} (hs : Scr s B Z)
    (hptr : s.gpr .t3 = off B (slot w 8 + 8 * i))
    (h1 : s.gpr .a1 = BitVec.ofNat 64 d)
    (hstride : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (hd : d < 16) (hi : i < w) (hZ : slot w 24 ≤ Z) :
    WP isa (.block (wordSelectHead ++ wordSelectPrefix 15 ++ wordSelectCell)) s fun t =>
      (t.gpr .s0 = word s.mem B (slot w (8 + d) + 8 * i) ∧ t.mem = s.mem) ∧
        Keep [.s0, .s1, .s2, .s3, .t2, .t6] s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (wordSelectHead_ok hptr h1 hd) fun t₁ ⟨⟨p1, v1, z1, b1, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wordSelectPrefix_ok (hs.congr k1.2.2) p1 b1 v1 z1
    ((k1.gpr (by decide)).trans hstride) hd hi hZ 15 (by decide))
    fun t₂ ⟨⟨v2, p2, b2, m2⟩, k2⟩ => ?_
  refine WP.mono (wordSelectCell_ok ((hs.congr k1.2.2).congr k2.2.2) p2 b2
    ((k2.gpr (by decide)).trans z1) (by decide) hd hi hZ) fun t ⟨⟨v3, m3⟩, k3⟩ => ?_
  refine ⟨⟨?_, m3.trans (m2.trans m1)⟩, ((k1.trans k2).trans k3).mono (by decide)⟩
  rw [v2, m2, m1] at v3
  by_cases he : 15 = d
  · simpa [he] using v3
  · simpa only [he, ↓reduceIte, show d < 15 by omega_arith, ↓reduceIte] using v3

/-- The registers the selection writes. -/
def selectRegs : List Reg := [.t3, .s4, .t5, .s1, .s0, .s3, .t6, .s2, .t2]

theorem wordSelect_shl2 (a : Nat) : BitVec.ofNat 64 a <<< 2 = BitVec.ofNat 64 (4 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- Initialize the two column pointers and the public word count. -/
theorem wordSelectInit_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) :
    WP isa (.block wordSelectInit) s fun t =>
      (t.gpr .t3 = off B (slot w 8) ∧ t.gpr .s4 = off B (slot w 5) ∧
        t.gpr .t5 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.t3, .s4, .t5] s t := by
  obtain e8 : slot w 0 + 8 * (8 * (w + 2)) = slot w 8 := by unfold slot; omega_arith
  obtain e5 : slot w 0 + (4 * (8 * (w + 2)) + 8 * (w + 2)) = slot w 5 := by unfold slot; omega_arith
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold wordSelectInit
  brun [h.a7, h.s5, h.t0, sqr_shl3, wordSelect_shl2, ← BitVec.ofNat_add, off_add, e8, e5]

/-- Store one selected word and advance the public pointers and counter. -/
theorem wordSelectStore_ok {s : State} {B : Addr} {Z w i : Nat} (hs : Scr s B Z)
    (hptr : s.gpr .s4 = off B (slot w 5 + 8 * i))
    (ht3 : s.gpr .t3 = off B (slot w 8 + 8 * i))
    (hi : i < w) (hZ : slot w 24 ≤ Z) :
    WP isa (.block (wordSelectStore ++ ([.addi .t5 .t5 (-1)] : List Instr))) s fun t =>
      (t.mem = s.mem.writeW (off B (slot w 5 + 8 * i)) (s.gpr .s0) ∧
        t.gpr .s4 = off B (slot w 5 + 8 * (i + 1)) ∧
        t.gpr .t3 = off B (slot w 8 + 8 * (i + 1)) ∧
        t.gpr .t5 = s.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep [.s4, .t3, .t5] s t := by
  obtain hs5 := slot_lt (w := w) (show 5 < 24 by decide)
  obtain hfit : slot w 5 + 8 * i + 8 ≤ Z := by omega_arith
  obtain hal : (slot w 5 + 8 * i) % 8 = 0 := by have := slot_al w 5; omega_arith
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold wordSelectStore
  brun [hptr, ht3, hs.st hfit, hs.al8 hfit hal, show slot w 5 + 8 * i + 8 = slot w 5 + 8 * (i + 1) by omega_arith,
    show slot w 8 + 8 * i + 8 = slot w 8 + 8 * (i + 1) by omega_arith]

/-- The word-oriented scan reads every table entry and changes only array 5. -/
theorem wordSelect_ok {s : State} {B : Addr} {Z w N d : Nat} (h : WCtx s B Z w N)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa wordSelect s fun t =>
      (A t.mem B w 5 = A s.mem B w (8 + d) ∧
        (∀ j < 24, j ≠ 3 → j ≠ 5 → A t.mem B w j = A s.mem B w j) ∧
        WCtx t B Z w N ∧ WinO B w s.mem t.mem) ∧ Keep selectRegs s t := by
  have hn := h.nw
  obtain hs5 := slot_lt (w := w) (show 5 < 24 by decide)
  obtain hsd := slot_lt (w := w) (show 8 + d < 24 by omega_arith)
  obtain sep := slot_lt (w := w) (show 5 < 8 + d by omega_arith)
  unfold wordSelect countLoop
  refine WP.seq (WP.mono (wordSelectInit_ok h) fun t₀ ⟨⟨p0, o0, c0, m0⟩, k0⟩ => ?_)
  let I : Nat → State → Prop := fun i t =>
    WCtx t B Z w N ∧ t.gpr .t3 = off B (slot w 8 + 8 * i) ∧
      t.gpr .s4 = off B (slot w 5 + 8 * i) ∧ Outside B (slot w 5) (8 * i) s.mem t.mem ∧
      wordsVal t.mem B (slot w 5) i = wordsVal s.mem B (slot w (8 + d)) i ∧ Keep selectRegs s t
  obtain init : I 0 t₀ := ⟨h.regs k0 (by decide) m0, by simpa using p0, by simpa using o0,
    by rw [m0]; exact Outside.refl _ _ _ _, by simp only [wordsVal], k0.mono (by decide)⟩
  refine WP.mono (wp_countdown (cnt := .t5) (N := w) (by have := h.w31; omega_arith)
    (by have := h.w2; omega_arith) I (fun i hi t ⟨ct, pt, po, ot, vt, kt⟩ hc => ?_) init c0)
    fun t ⟨ct, _, _, ot, vt, kt⟩ => ⟨⟨vt, fun j hj _ h5 => arr_out ot hj h5 hn,
      ct, arrO ot (by decide) (by decide)⟩, kt⟩
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (wordSelectWord_ok ct.scr pt ((kt.gpr (by decide)).trans h1) ct.s5 hd hi ct.hZ)
    fun u ⟨⟨vu, mu⟩, ku⟩ => ?_
  obtain cu := ct.regs ku (by decide) mu
  obtain val_old : word t.mem B (slot w (8 + d) + 8 * i) = word s.mem B (slot w (8 + d) + 8 * i) :=
    ot.word (Or.inr (by omega_arith)) (by omega_arith)
  obtain val : u.gpr .s0 = word s.mem B (slot w (8 + d) + 8 * i) := vu.trans val_old
  refine WP.mono (wordSelectStore_ok cu.scr ((ku.gpr (by decide)).trans po)
    ((ku.gpr (by decide)).trans pt) hi cu.hZ) fun v ⟨⟨mv, pv, qv, cv⟩, kv⟩ => ?_
  rw [mu, val] at mv
  obtain ov : Outside B (slot w 5 + 8 * i) 8 t.mem v.mem := by
    rw [mv]; exact writeW_outside _ _ _ (by omega_arith)
  obtain ov_full : Outside B (slot w 5) (8 * w) t.mem v.mem := ov.mono (by omega_arith) (by omega_arith)
  obtain cv' := cu.of kv (by decide) (by rw [mu]; exact arrO ov_full (by decide) (by decide))
  refine ⟨⟨cv', qv, pv, ?_, ?_, ((kt.trans ku).trans kv).mono (by decide)⟩, ?_⟩
  · exact (ot.mono (Nat.le_refl _) (by omega_arith)).trans (ov.mono (by omega_arith) (by omega_arith))
  · rw [mv, fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), vt, wordsVal_succ_top]
  · rw [cv, ku.gpr (by decide)]

/-- `select`: array 5 := `T_d`, for `d` in `a1`; only arrays 3 and 5 change. -/
theorem select_ok {s : State} {B : Addr} {Z w N d : Nat} (h : WCtx s B Z w N)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa select s fun t =>
      (A t.mem B w 5 = A s.mem B w (8 + d) ∧ (∀ j < 24, j ≠ 3 → j ≠ 5 → A t.mem B w j = A s.mem B w j) ∧
        WCtx t B Z w N ∧ WinO B w s.mem t.mem) ∧ Keep selectRegs s t := by
  exact wordSelect_ok h h1 hd

/-! ## Windows -/

/-- Every array but 2, 3, 5 and 6 keeps its number. -/
def Fix (B : Addr) (w : Nat) (m m' : Mem) : Prop :=
  ∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ 5 → j ≠ 6 → A m' B w j = A m B w j

theorem Fix.trans {B : Addr} {w : Nat} {m₁ m₂ m₃ : Mem} (a : Fix B w m₁ m₂) (b : Fix B w m₂ m₃) : Fix B w m₁ m₃ :=
  fun j hj h2 h3 h5 h6 => (b j hj h2 h3 h5 h6).trans (a j hj h2 h3 h5 h6)

/-- The registers a window writes. -/
def winRegs : List Reg := Pub.montRegs ++ sqRegs ++ selectRegs ++ [.a1, .s7]

/-- A square of `a` in the context. -/
theorem sq_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : A s.mem B w 6 < N) {X c : Nat} :
    WP isa (sqrOp 6 6 5) s fun t =>
      (WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧ Fix B w s.mem t.mem ∧ A t.mem B w 6 < N ∧
        (A s.mem B w 6 % N = X ^ c * 2 ^ (64 * w) % N →
          A t.mem B w 6 % N = X ^ (c + c) * 2 ^ (64 * w) % N)) ∧ Keep sqRegs s t := by
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  exact WP.mono (h.sqr (o := 6) (a := 6) (p := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha)
    fun t ⟨⟨ct, lt, e, v, o⟩, k⟩ =>
    ⟨⟨ct, o, fun j hj h2 h3 h5 h6 => v j hj h2 h3 h5 h6, lt, fun hA => mont_pow hR hA hA e⟩, k⟩

theorem top_nibble (x : BitVec 64) : x >>> 60 = BitVec.ofNat 64 (x.toNat / 2 ^ 60) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  omega_arith

/-- `window`. -/
theorem window_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) (hodd : N % 2 = 1)
    (ha : A s.mem B w 6 < N) (htab : ∀ i < 16, A s.mem B w (8 + i) < N) {X c : Nat} :
    WP isa window s fun t =>
      (WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧ Fix B w s.mem t.mem ∧ A t.mem B w 6 < N ∧
        t.gpr .s7 = s.gpr .s7 <<< 4 ∧
        (A s.mem B w 6 % N = X ^ c * 2 ^ (64 * w) % N →
          (∀ i < 16, A s.mem B w (8 + i) % N = X ^ i * 2 ^ (64 * w) % N) →
          A t.mem B w 6 % N = X ^ (16 * c + (s.gpr .s7).toNat / 2 ^ 60) * 2 ^ (64 * w) % N)) ∧
        Keep winRegs s t := by
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold window
  refine WP.seq (WP.mono (sq_ok h hodd ha (X := X) (c := c)) fun s₁ ⟨⟨c1, o1, f1, l1, e1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c1 hodd l1 (X := X) (c := c + c)) fun s₂ ⟨⟨c2, o2, f2, l2, e2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c2 hodd l2 (X := X) (c := c + c + (c + c)))
    fun s₃ ⟨⟨c3, o3, f3, l3, e3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c3 hodd l3 (X := X) (c := c + c + (c + c) + (c + c + (c + c))))
    fun s₄ ⟨⟨c4, o4, f4, l4, e4⟩, k4⟩ => ?_)
  obtain k14 := ((k1.trans k2).trans k3).trans k4
  obtain f14 := (f1.trans f2).trans (f3.trans f4)
  obtain hd := (s.gpr .s7).isLt
  obtain hd16 : (s.gpr .s7).toNat / 2 ^ 60 < 16 := by omega_arith
  refine WP.seq (WP.mono (WP.keep [.a1] (Q := fun t =>
      t.gpr .a1 = BitVec.ofNat 64 ((s.gpr .s7).toNat / 2 ^ 60) ∧ t.mem = s₄.mem)
    (by brun [top_nibble, k14.gpr (r := .s7) (by decide)]) (by rfl) (by rfl)) fun s₅ ⟨⟨a1, m5⟩, k5⟩ => ?_)
  obtain c5 := c4.regs k5 (by decide) m5
  refine WP.seq (WP.mono (select_ok c5 a1 hd16) fun s₆ ⟨⟨a6, v6, c6, o6⟩, k6⟩ => ?_)
  obtain A6 : A s₆.mem B w 6 = A s₄.mem B w 6 := by rw [v6 6 (by decide) (by decide) (by decide), m5]
  rw [m5, f14 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)] at a6
  refine WP.seq (WP.mono (c6.mont (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [a6]; exact htab _ hd16))
    fun s₇ ⟨⟨c7, l7, e7, v7, o7⟩, k7⟩ => ?_)
  refine WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = s₇.gpr .s7 <<< 4 ∧ t.mem = s₇.mem)
    (by brun) (by rfl) (by rfl)) fun t ⟨⟨a7, mt⟩, kt⟩ =>
      ⟨⟨c7.regs kt (by decide) mt, ?_, ?_, by rw [mt]; exact l7, ?_, ?_⟩, ?_⟩
  · rw [mt]
    exact ((((o1.trans o2).trans (o3.trans o4)).trans (by rw [← m5]; exact o6)).trans o7)
  · intro j hj h2 h3 h5 h6
    rw [mt, v7 j hj h2 h3 h6, v6 j hj h3 h5, m5]
    exact f14 j hj h2 h3 h5 h6
  · rw [a7, k7.gpr (by decide), k6.gpr (by decide), k5.gpr (by decide), k14.gpr (by decide)]
  · intro hA hT
    rw [mt]
    rw [A6] at e7
    have := mont_pow hR (e4 (e3 (e2 (e1 hA)))) (by rw [a6]; exact hT _ hd16) e7
    rw [this, show c + c + (c + c) + (c + c + (c + c)) + (c + c + (c + c) + (c + c + (c + c))) = 16 * c by omega_arith]
  · exact ((((k14.trans k5).trans k6).trans k7).trans kt).mono (by decide)

/-! ## The exponent -/

/-- The registers `powWin` writes. -/
def powWRegs : List Reg := tabRegs ++ winRegs ++ [.s9, .s10]

theorem Keep.within {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h : Keep rs s₁ s₂) (h' : Keep rs' s₂ s₃)
    (hs : ∀ r ∈ rs', r ∈ rs) : Keep rs s₁ s₃ :=
  (h.trans h').mono fun r hr => (List.mem_append.1 hr).elim id (hs r)

theorem win_pow {r : Reg} (h : r ∈ winRegs) : r ∈ powWRegs :=
  List.mem_append_left _ (List.mem_append_right _ h)

/-- After the table (`t₀`), with `c` of the exponent scanned: what the
windows keep. -/
structure Run (s₀ t₀ u : State) (B : Addr) (Z w N X RR c : Nat) : Prop where
  ctx : WCtx u B Z w N
  out : WinO B w s₀.mem u.mem
  fix : Fix B w t₀.mem u.mem
  lt : A u.mem B w 6 < N
  pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A u.mem B w 6 % N = X ^ c * 2 ^ (64 * w) % N
  keep : Keep powWRegs s₀ u

theorem lbu_ok {u : State} {D : Addr} {i : Nat} (h9 : u.gpr .s9 = off D i)
    (hrd : InRegions (u.rd ++ u.wr) (off D i) 1) :
    WP isa (.block [.load .b .s7 .s9 0, .shift .sll .d .s7 .s7 56, .addi .s9 .s9 1]) u fun t =>
      (t.gpr .s7 = BitVec.ofNat 64 (u.mem (off D i)).toNat <<< 56 ∧ t.gpr .s9 = off D (i + 1) ∧
        t.mem = u.mem) ∧ Keep [.s7, .s9] u t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h9, hrd, read_byte64, add_ofNat_zero]

theorem nib_hi {b : Nat} (hb : b < 256) : (BitVec.ofNat 64 b <<< 56).toNat / 2 ^ 60 = b / 16 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega_arith

theorem nib_lo (b : Nat) : (BitVec.ofNat 64 b <<< 56 <<< 4).toNat / 2 ^ 60 = b % 16 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega_arith

/-- `byteWin`: the two windows of the byte `b` at `s9`, `c := 256 c + b`. -/
theorem byteWin_ok {s₀ t₀ u : State} {B D : Addr} {Z w N X RR c i : Nat} (hodd : N % 2 = 1)
    (htab : TabUpTo t₀.mem B w N X RR 16) (h : Run s₀ t₀ u B Z w N X RR c) (h9 : u.gpr .s9 = off D i)
    (hrd : InRegions (u.rd ++ u.wr) (off D i) 1) :
    WP isa byteWin u fun t =>
      Run s₀ t₀ t B Z w N X RR (256 * c + (u.mem (off D i)).toNat) ∧ t.gpr .s9 = off D (i + 1) ∧
        t.gpr .s10 = u.gpr .s10 := by
  generalize hb : (u.mem (off D i)).toNat = b
  obtain hb256 : b < 256 := by rw [← hb]; exact (u.mem (off D i)).isLt
  obtain tab : ∀ {m : Mem}, Fix B w t₀.mem m → ∀ i < 16, A m B w (8 + i) < N ∧
      (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A m B w (8 + i) % N = X ^ i * 2 ^ (64 * w) % N) :=
    fun hf i hi => by
      rw [hf (8 + i) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact htab i hi
  unfold byteWin
  refine WP.seq (WP.mono (lbu_ok h9 hrd) fun u₁ ⟨⟨a7, a9, m1⟩, k1⟩ => ?_)
  rw [hb] at a7
  obtain c1 := h.ctx.regs k1 (by decide) m1
  obtain f1 : Fix B w t₀.mem u₁.mem := by rw [m1]; exact h.fix
  refine WP.seq (WP.mono (window_ok c1 hodd (by rw [m1]; exact h.lt) (fun i hi => (tab f1 i hi).1)
    (X := X) (c := c)) fun u₂ ⟨⟨c2, o2, f2, l2, a7', e2⟩, k2⟩ => ?_)
  refine WP.mono (window_ok c2 hodd l2 (fun i hi => (tab (f1.trans f2) i hi).1) (X := X) (c := 16 * c + b / 16))
    fun t ⟨⟨c3, o3, f3, l3, _, e3⟩, k3⟩ => ⟨⟨c3, ?_, f1.trans (f2.trans f3), l3, fun hE => ?_, ?_⟩, ?_, ?_⟩
  · rw [m1] at o2; exact (h.out.trans o2).trans o3
  · have p1 := e2 (by rw [m1]; exact h.pw hE) (fun i hi => (tab f1 i hi).2 hE)
    rw [a7, nib_hi hb256] at p1
    obtain p2 := e3 p1 (fun i hi => (tab (f1.trans f2) i hi).2 hE)
    rw [a7', a7, nib_lo b] at p2
    rw [p2, show 16 * (16 * c + b / 16) + b % 16 = 256 * c + b by omega_arith]
  · exact Keep.within (Keep.within (Keep.within h.keep k1 (by decide)) k2 fun _ => win_pow) k3 fun _ => win_pow
  · rw [k3.gpr (by decide), k2.gpr (by decide), a9]
  · rw [k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)]

/-- `powWin`: `x^d mod m` into array 4, for `x` in array 4, `m` (odd, at least
2) in array 0, something below `m` in array 1 (if `R² mod m`, the result is
right) and the `L ≥ 1` bytes of `d` at `D` (`s9`, `s10`), apart from the
working space of 24 arrays, of which it writes only arrays 1–23, keeping array 1's
value. -/
theorem powWin1_ok {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 24 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hN : 2 ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1)
    (hRRlt : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w)
    (h9 : s.gpr .s9 = off D 0) (h10 : s.gpr .s10 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, VG.Proof.Bignum.ofs B x < Z → off D i ≠ x) :
    WP isa powWin s fun t =>
      ((wordsVal s.mem B (slot w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w →
          wordsVal t.mem B (slot w 4) w =
            wordsVal s.mem B (slot w 4) w ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) %
              wordsVal s.mem B (slot w 0) w) ∧
        WinO B w s.mem t.mem ∧ wordsVal t.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w) ∧
      Keep powWRegs s t := by
  obtain h0 : WCtx s B Z w (A s.mem B w 0) := ⟨hs, hw2, hw', hZ, h7, h5, ht0, hinv, rfl⟩
  have hn := h0.nw
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd hRRlt ⊢
  replace h0 : WCtx s B Z w N := hNd ▸ h0
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hXd : wordsVal s.mem B (slot w 4) w = X
  generalize hRRd : wordsVal s.mem B (slot w 1) w = RR at hRRlt ⊢
  unfold powWin
  refine WP.seq (WP.mono (table_ok h0 hN hodd (by rw [show A s.mem B w 1 = RR from hRRd]; exact hRRlt))
    fun t₀ ⟨⟨c0, o0, t01, _, t7, a6, htab⟩, k0⟩ => ?_)
  rw [show A s.mem B w 4 = X from hXd, show A s.mem B w 1 = RR from hRRd] at htab
  obtain r0 : Run s t₀ t₀ B Z w N X RR 0 := ⟨c0, o0, fun _ _ _ _ _ _ => rfl, by rw [a6]; exact (htab 0 (by decide)).1,
    fun hE => by rw [a6]; exact (htab 0 (by decide)).2 hE, k0.mono (by decide)⟩
  -- The bytes.
  let Inv : Nat → State → Prop := fun i u =>
    Run s t₀ u B Z w N X RR (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D i)) ∧ u.gpr .s9 = off D i
  refine WP.seq (WP.mono (wp_countdown (cnt := .s10) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi u ⟨hu, u9⟩ _ => ?_) ⟨by simpa [Spec.Rsa.bytesAt, Spec.Rsa.os2ip] using r0,
      by rw [k0.gpr (by decide), h9]⟩
    (by rw [k0.gpr (by decide), h10])) fun u ⟨hu, _⟩ => ?_)
  · have hb : u.mem (off D i) = s.mem (off D i) := by
      refine hu.out _ ?_
      have := slot_lt (w := w) (show 1 < 24 by decide)
      obtain e24 := slot24 w
      right
      by_contra hc
      exact hsep i hi (off D i) (by simp only [VG.Proof.Bignum.ofs] at hc ⊢; omega_arith) rfl
    refine WP.seq (WP.mono (byteWin_ok hodd htab hu u9 (by rw [hu.keep.2.1, hu.keep.2.2]; exact hrd i hi))
      fun u₁ ⟨hu₁, a9, a10⟩ => ?_)
    refine WP.mono (dec_ok u₁ .s10) fun u₂ e => ?_
    subst e
    refine ⟨⟨⟨hu₁.ctx.regs (Keep.write _ _ _) (by decide) (by rw [mem_write]), by rw [mem_write]; exact hu₁.out,
        by rw [mem_write]; exact hu₁.fix, by rw [mem_write]; exact hu₁.lt, fun hE => ?_,
        Keep.within hu₁.keep (Keep.write _ _ _) (by decide)⟩, by gsimp; exact a9⟩, by gsimp; rw [a10]⟩
    rw [mem_write, hu₁.pw hE, hb, Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc]
  -- Out of Montgomery form.
  obtain t7' : A u.mem B w 7 = 1 := by rw [hu.fix 7 (by decide) (by decide) (by decide) (by decide) (by decide), t7]
  refine WP.mono (hu.ctx.mont (o := 4) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [t7']; omega_arith)) fun t ⟨⟨_, lt, e, v, o⟩, k⟩ =>
    ⟨⟨fun hE => ?_, hu.out.trans o, ?_⟩, Keep.within hu.keep k fun _ h => win_pow (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))⟩
  · rw [t7', Nat.mul_one] at e
    refine (Nat.mod_eq_of_lt lt).symm.trans ?_
    exact VG.Proof.Bignum.mont_cancel hR (by rw [e, hu.pw hE])
  · show A t.mem B w 1 = RR
    rw [v 1 (by decide) (by decide) (by decide) (by decide),
      hu.fix 1 (by decide) (by decide) (by decide) (by decide) (by decide), t01, ← hRRd]

/-- `powWin`, without what it leaves in array 1. -/
theorem powWin_ok {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 24 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hN : 2 ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1)
    (hRRlt : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w)
    (h9 : s.gpr .s9 = off D 0) (h10 : s.gpr .s10 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, VG.Proof.Bignum.ofs B x < Z → off D i ≠ x) :
    WP isa powWin s fun t =>
      ((wordsVal s.mem B (slot w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w →
          wordsVal t.mem B (slot w 4) w =
            wordsVal s.mem B (slot w 4) w ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) %
              wordsVal s.mem B (slot w 0) w) ∧
        WinO B w s.mem t.mem) ∧ Keep powWRegs s t :=
  WP.mono (powWin1_ok hs hw2 hw' hZ h7 h5 ht0 hinv hN hodd hRRlt h9 h10 hL hL' hrd hsep)
    fun _ ⟨⟨hp, o, _⟩, k⟩ => ⟨⟨hp, o⟩, k⟩

/-! ## In radix `2⁵⁷` -/

open VG.Impl.Bignum.RISCV64.Pow57 VG.Proof.Bignum.RISCV64.Pow57

/-- `R'`, the radix of the Montgomery form. -/
abbrev R57 (q : Nat) : Nat := 2 ^ (513 * q)

/-- The context of the operations in radix `2⁵⁷`. -/
theorem WCtx.sp {s : State} {B : Addr} {Z w N q : Nat} (h : WCtx s B Z w N) (hw : w = 8 * q) (q2 : 2 ≤ q) (q6 : q ≤ 6) :
    Sp s B Z q (slot w 0) := by
  subst hw
  refine ⟨h.scr, q2, q6, slot_al _ _, ?_, h.a7, ?_⟩
  · have := h.hZ; unfold slot Impl.Bignum.hdrBytes at *; omega_using [this, q2]
  · rw [h.s5]; exact congrArg _ (by omega_using [])

theorem slot_at {w q j : Nat} (hw : w = 8 * q) : slot w j = slot w 0 + j * (64 * q + 16) := by
  subst hw; unfold slot; rw [show 8 * (8 * q + 2) = 64 * q + 16 by omega_using []]; omega_using []

theorem slot2 {w q : Nat} (hw : w = 8 * q) : slot w 2 = oM q (slot w 0) := by
  rw [slot_at hw]; unfold oM; omega_using []

theorem slot5 {w q : Nat} (hw : w = 8 * q) : slot w 5 = o5 q (slot w 0) := by
  rw [slot_at hw]; unfold o5; omega_using []

theorem slot6 {w q : Nat} (hw : w = 8 * q) : slot w 6 = o6 q (slot w 0) := by
  rw [slot_at hw]; unfold o6; omega_using []

/-- Arrays 2 to 7: what the operations in radix `2⁵⁷` write. -/
abbrev Low (B : Addr) (w : Nat) (m m' : Mem) : Prop := Mont.Outside B (slot w 2) (6 * (8 * (w + 2))) m m'

theorem Low.win {B : Addr} {w : Nat} {m m' : Mem} (h : Low B w m m') : WinO B w m m' :=
  Mont.Outside.mono h (by unfold slot; omega_arith) (by unfold slot; omega_arith)

theorem Low.arr {B : Addr} {w j : Nat} {m m' : Mem} (h : Low B w m m') (hj : j < 24) (h' : j < 2 ∨ 8 ≤ j)
    (hn : B.toNat + slot w 24 ≤ 2 ^ 64) : A m' B w j = A m B w j := by
  have := slot_lt (w := w) hj
  refine Mont.Outside.wordsVal h ?_ (by omega_arith)
  rcases h' with h' | h'
  · have := slot_lt (w := w) (show j < 2 by omega_using [h'])
    omega_arith
  · right
    obtain l := Nat.mul_le_mul_right (8 * (w + 2)) h'
    unfold slot
    omega_using [l]

theorem Low.of_out {B : Addr} {w q o n : Nat} {m m' : Mem} (hw : w = 8 * q) (h : Mont.Outside B o n m m')
    (h1 : oM q (slot w 0) ≤ o) (h2 : o + n ≤ oM q (slot w 0) + 384 * q + 96) : Low B w m m' :=
  Mont.Outside.mono h (by rw [slot2 hw]; exact h1) (by rw [slot2 hw]; omega_using [h2, hw])

theorem Low.of_arr {B : Addr} {w o : Nat} {m m' : Mem} (h : Arrays B w [o] m m') (h1 : 2 ≤ o) (h2 : o < 8) : Low B w m m' :=
  fun x hx => h x fun j hj => by
    obtain rfl : j = o := by simpa using hj
    obtain l := Nat.mul_le_mul_right (8 * (w + 2)) h1
    obtain l' := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ 8 from h2)
    rw [Nat.add_mul, Nat.one_mul] at l'
    simp only [VG.Proof.Bignum.ofs, Mont.ofs] at hx ⊢
    unfold slot at hx ⊢
    omega_using [hx, l, l']

/-- The context after code that writes arrays 1–23 and leaves the registers as they were. -/
theorem WCtx.op {s t : State} {B : Addr} {Z w N q : Nat} (h : WCtx s B Z w N) (hw : w = 8 * q) (k : Keep opRegs s t)
    (h0 : t.gpr .t0 = BitVec.ofNat 64 (8 * q)) (o : Low B w s.mem t.mem) : WCtx t B Z w N := by
  have hn := h.nw
  obtain s0 := slot_lt (w := w) (show 0 < 24 by decide)
  obtain s2 := slot_lt (w := w) (show 0 < 2 by decide)
  refine ⟨h.scr.congr k.2.2, h.w2, h.w31, h.hZ, (k.gpr (by decide)).trans h.a7, (k.gpr (by decide)).trans h.s5,
    by rw [h0, hw], ?_, (Low.arr o (by decide) (.inl (by decide)) hn).trans h.n⟩
  rw [k.gpr (by decide), Mont.Outside.word o (Or.inl (by omega_arith)) (by omega_arith)]
  exact h.inv

/-- A copy (or selection) of `w` words into array 5. -/
theorem Low.of5 {B : Addr} {w : Nat} {m m' : Mem} (h : Mont.Outside B (slot w 5) (8 * w) m m') : Low B w m m' :=
  Mont.Outside.mono h (by unfold slot; omega_arith) (by unfold slot; omega_arith)

/-! ### The table -/

theorem pow2q_ok {s : State} {B : Addr} {Z w N q : Nat} (h : WCtx s B Z w N) (hw : w = 8 * q) (q6 : q ≤ 6) :
    WP isa pow2q s fun t => (A t.mem B w 7 = 2 ^ q ∧ Mont.Outside B (slot w 7) (8 * w) s.mem t.mem) ∧
      Keep [.s0, .t3, .t5, .t2] s t := by
  have hn := h.nw
  have hw2 := h.w2
  obtain s7 := slot_lt (w := w) (show 7 < 24 by decide)
  have hZ := h.hZ
  unfold pow2q
  refine WP.seq (WP.mono (Pub.oneP_ok h.scr (by omega_arith) h.w31
    (Nat.le_trans (by unfold slot; omega_arith) h.hZ) h.a7 h.s5 h.t0) fun s₁ ⟨⟨h7, o1⟩, k1⟩ => ?_)
  replace h7 : A s₁.mem B w 7 = 1 := h7
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) ((k1.gpr (by decide)).trans h.a7) ((k1.gpr (by decide)).trans h.s5) 7)
    fun s₂ ⟨⟨a3, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  obtain e1 : BitVec.ofNat 64 w >>> 3 = BitVec.ofNat 64 q := by
    rw [srl_ofNat (by have := h.w31; omega_using [this]), hw]; exact congrArg _ (by omega_using [])
  obtain e2 : (BitVec.ofNat 64 q).toNat % 64 = q := by rw [BitVec.toNat_ofNat]; omega_using [q6]
  obtain e3 : BitVec.ofNat 64 1 <<< q = BitVec.ofNat 64 (2 ^ q) := by rw [sll_ofNat, Nat.one_mul]
  obtain r : WP isa (.block [.shift .srl .d .t2 .t0 3, .li .s0 1, .shiftReg .sll .d .s0 .s0 .t2, .store .d .s0 .t3 0]) s₂ fun t =>
      t.mem = s₂.mem.writeW (off B (slot w 7)) (BitVec.ofNat 64 (2 ^ q)) ∧ Keep [.t2, .s0] s₂ t := by
    obtain hs := h.scr.congr k12.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [a3, (k12.gpr (r := .t0) (by decide)).trans h.t0, e1, e2, e3, exec_li, ↓exec_sllReg', hs.st (show slot w 7 + 8 ≤ Z by omega_arith),
      hs.al8 (show slot w 7 + 8 ≤ Z by omega_arith) (slot_al w 7)]
  refine WP.mono r fun t ⟨tm, kt⟩ => ⟨⟨?_, ?_⟩, (k12.trans kt).mono (by decide)⟩
  · obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega_arith⟩
    rw [m2] at tm
    unfold A at h7 ⊢
    rw [wordsVal] at h7
    obtain p : 2 ^ q ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) q6
    obtain z : wordsVal s₁.mem B (slot (w' + 1) 7 + 8) w' = 0 := by omega_using [h7]
    rw [wordsVal, tm, Mont.word_writeW_self, (Mont.writeW_outside s₁.mem B _ (by omega_arith)).wordsVal (Or.inr (Nat.le_refl _)) (by omega_arith), z,
      BitVec.toNat_ofNat]
    omega_using [p]
  · rw [tm, m2]
    exact Mont.Outside.trans o1 ((Mont.writeW_outside _ B _ (by omega_arith)).mono (Nat.le_refl _) (by omega_arith))

/-- The table's entries below `j`, if `R² mod m` is right. -/
def Tab57 (m : Mem) (B : Addr) (w q N X RR j : Nat) : Prop :=
  ∀ i < j, A m B w (8 + i) < N ∧ (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A m B w (8 + i) % N = X ^ i * R57 q % N)

theorem mont57 {o a b X i q R N : Nat} (hR : Nat.Coprime R N) (ha : a % N = X ^ i * R57 q % N)
    (hb : b % N = X * R % N) (h : o * R % N = a * b % N) : o % N = X ^ (i + 1) * R57 q % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [h, Nat.mul_mod, ha, hb, ← Nat.mul_mod, Nat.pow_succ]
  congr 1
  ac_rfl

/-- `table57`. -/
theorem table57_ok {s : State} {B : Addr} {Z w N q : Nat} (h : WCtx s B Z w N) (hw : w = 8 * q) (q6 : q ≤ 6) (hodd : N % 2 = 1)
    (hRR : A s.mem B w 1 < N) :
    WP isa table57 s fun t =>
      (WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧ A t.mem B w 1 = A s.mem B w 1 ∧
        Tab57 t.mem B w q N (A s.mem B w 4) (A s.mem B w 1) 16) ∧ Keep tabRegs s t := by
  have hn := h.nw
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hX : A s.mem B w 4 = X
  generalize hRRd : A s.mem B w 1 = RR at hRR
  unfold table57
  -- `2^q` in array 7.
  refine WP.seq (WP.mono (pow2q_ok h hw q6) fun s₁ ⟨⟨h7, o1⟩, k1⟩ => ?_)
  obtain c1 := h.of k1 (by decide) (arrO o1 (by decide) (by decide))
  obtain R1 : A s₁.mem B w 1 = RR := by rw [arr_out o1 (by decide) (by decide) hn, hRRd]
  obtain X1 : A s₁.mem B w 4 = X := by rw [arr_out o1 (by decide) (by decide) hn, hX]
  -- `T_0 = R' mod m`.
  refine WP.seq (WP.mono (c1.mont (o := 8) (a := 7) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R1]; exact hRR)) fun s₂ ⟨⟨c2, lt2, e2, v2, o2⟩, k2⟩ => ?_)
  rw [h7, R1] at e2
  obtain T0 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₂.mem B w 8 % N = X ^ 0 * R57 q % N :=
    fun hE => by
      refine VG.Proof.Bignum.mont_cancel hR ?_
      rw [e2, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_zero, Nat.one_mul, ← Nat.mul_assoc, ← Nat.pow_add,
        show q + 64 * w = 513 * q by omega_using [hw]]
  obtain R2 : A s₂.mem B w 1 = RR := by rw [v2 1 (by decide) (by decide) (by decide) (by decide), R1]
  obtain X2 : A s₂.mem B w 4 = X := by rw [v2 4 (by decide) (by decide) (by decide) (by decide), X1]
  -- `x R mod m`.
  refine WP.seq (WP.mono (c2.mont (o := 4) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R2]; exact hRR))
    fun s₃ ⟨⟨c3, lt3, e3, v3, o3⟩, k3⟩ => ?_)
  rw [X2, R2] at e3
  obtain T1 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₃.mem B w 4 % N = X * 2 ^ (64 * w) % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [e3, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  obtain R3 : A s₃.mem B w 1 = RR := by rw [v3 1 (by decide) (by decide) (by decide) (by decide), R2]
  obtain E3 : A s₃.mem B w 8 = A s₂.mem B w 8 := v3 8 (by decide) (by decide) (by decide) (by decide)
  -- `a := T_0`.
  refine WP.seq (WP.mono (copy_ok c3 (o := 6) (a := 8) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨a4, o4⟩, k4⟩ => ?_)
  obtain c4 := c3.of k4 (by decide) (arrO o4 (by decide) (by decide))
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = BitVec.ofNat 64 1 ∧ t.mem = s₄.mem)
    (by brun [Pub.pub_li1, exec_li]) (by rfl) (by rfl)) fun s₅ ⟨⟨a7, m5⟩, k5⟩ => ?_)
  obtain c5 := c4.regs k5 (by decide) m5
  obtain O5 : WinO B w s.mem s₅.mem := by
    rw [m5]
    exact (((arrO o1 (by decide) (by decide)).trans o2).trans o3).trans (arrO o4 (by decide) (by decide))
  obtain K : ∀ j, j < 24 → j ≠ 6 → A s₅.mem B w j = A s₃.mem B w j := fun j hj h6 => by
    rw [m5]; exact arr_out o4 hj h6 hn
  obtain tab1 : Tab57 s₅.mem B w q N X RR 1 := by
    intro i hi
    obtain rfl : i = 0 := by omega_arith
    rw [K 8 (by decide) (by decide), E3]
    exact ⟨lt2, T0⟩
  obtain a5 : A s₅.mem B w 6 = A s₂.mem B w 8 := by rw [m5, a4, E3]
  refine WP.mono (count_loop (n := 15) (cr := .t2) (by decide)
      (fun k t => WCtx t B Z w N ∧ WinO B w s.mem t.mem ∧ t.gpr .s7 = BitVec.ofNat 64 (1 + k) ∧
        A t.mem B w 1 = RR ∧ A t.mem B w 4 = A s₃.mem B w 4 ∧
        Tab57 t.mem B w q N X RR (1 + k) ∧ A t.mem B w 6 < N ∧
        (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A t.mem B w 6 % N = X ^ k * R57 q % N) ∧
        Keep tabRegs s t)
      (fun k hk t ⟨ct, ot, t7, t1, t4, ttab, t6l, t6, kt⟩ => ?_)
      ⟨c5, O5, a7, by rw [K 1 (by decide) (by decide), R3], K 4 (by decide) (by decide), tab1,
        by rw [a5]; exact lt2, fun hE => by rw [a5]; exact T0 hE,
        ((((k1.trans k2).trans k3).trans k4).trans k5).mono (by decide)⟩)
    fun t ⟨ct, ot, _, t1, _, ttab, _, _, kt⟩ => ⟨⟨ct, ot, t1, ttab⟩, kt⟩
  refine WP.seq (WP.mono (ct.mont (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [t4]; exact lt3))
    fun u ⟨⟨cu, lu, eu, vu, ou⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (toEntry_ok cu (j := 1 + k) (by rw [ku.gpr (by decide), t7]) (by omega_arith))
    fun x ⟨⟨xe, xo⟩, kx⟩ => ?_)
  obtain cx := cu.of kx (by decide) (arrO xo (by omega_arith) (by omega_arith))
  obtain hend : WP isa (.block [.addi .s7 .s7 1, .addi .t2 .s7 (-16)]) x fun y =>
      (y.gpr .s7 = BitVec.ofNat 64 (1 + k) + BitVec.ofNat 64 1 ∧
        y.gpr .t2 = BitVec.ofNat 64 (1 + k) + BitVec.ofNat 64 1 - BitVec.ofNat 64 16 ∧ y.mem = x.mem) ∧
        Keep [.s7, .t2] x y := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(kx.gpr (r := .s7) (by decide)).trans ((ku.gpr (r := .s7) (by decide)).trans t7)]
  obtain M : ∀ j, j < 24 → j ≠ 2 → j ≠ 3 → j ≠ 6 → j ≠ 8 + (1 + k) → A x.mem B w j = A t.mem B w j :=
    fun j hj h2 h3 h6 he => by rw [arr_out xo hj he hn, vu j hj h2 h3 h6]
  obtain pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A u.mem B w 6 % N = X ^ (k + 1) * R57 q % N :=
    fun hE => mont57 hR (t6 hE) (by rw [t4]; exact T1 hE) eu
  refine WP.mono hend fun y ⟨⟨y7, y2, ym⟩, ky⟩ =>
    ⟨⟨cx.regs ky (by decide) ym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [ym]; exact (ot.trans ou).trans (arrO xo (by omega_arith) (by omega_arith))
  · rw [y7, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [ym, M 1 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t1]
  · rw [ym, M 4 (by decide) (by decide) (by decide) (by decide) (by omega_arith), t4]
  · intro i hi
    rw [ym]
    rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < 1 + k + 1 by omega_arith) with hi | rfl
    · rw [M (8 + i) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact ttab i hi
    · rw [xe]
      exact ⟨lu, fun hE => by rw [pw hE, Nat.add_comm 1 k]⟩
  · rw [ym, arr_out xo (by decide) (by omega_arith) hn]; exact lu
  · intro hE
    rw [ym, arr_out xo (by decide) (by omega_arith) hn, pw hE]
  · exact (((kt.trans ku).trans kx).trans ky).mono (by decide)
  · rw [y2, ← BitVec.ofNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

/-! ### The windows -/

/-- The operations' context, after the table (`t₀`), with `A ≡ X^c R'`. -/
structure Run57 (t₀ u : State) (B : Addr) (Z w N q X RR c : Nat) : Prop where
  ctx : WCtx u B Z w N
  mod : Mod57 u B q (slot w 0) N
  low : Low B w t₀.mem u.mem
  acc : ∃ a, AIn u.mem B q (oM q (slot w 0)) a ∧ a < 2 * N ∧
    (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → a % N = X ^ c * R57 q % N)

/-- `M`, its inverse and `A` after code that writes neither. -/
theorem Run57.of {t₀ u v : State} {B : Addr} {Z w N q X RR c : Nat} {rs : List Reg} (h : Run57 t₀ u B Z w N q X RR c) (hw : w = 8 * q)
    (q2 : 2 ≤ q) (q6 : q ≤ 6) (cv : WCtx v B Z w N) (k : Keep rs u v) (h1 : Reg.t1 ∉ rs) {o n : Nat}
    (out : Mont.Outside B o n u.mem v.mem) (ho : oT q (oM q (slot w 0)) ≤ o) (hn : o + n ≤ oM q (slot w 0) + 384 * q + 96) :
    Run57 t₀ v B Z w N q X RR c := by
  obtain sp := h.ctx.sp hw q2 q6
  obtain fit := sp.fit
  obtain ⟨a, hA, ha, e⟩ := h.acc
  obtain hn' := h.ctx.scr.nowrap
  refine ⟨cv, ⟨h.mod.mod.of k h1 out (by unfold oT at ho; omega_using [ho]) h.ctx.scr (by unfold oM; omega_using [fit]) (by omega_using [q2]),
    h.mod.pos, h.mod.lt⟩, Mont.Outside.trans h.low (Low.of_out hw out (by unfold oT at ho; omega_using [ho]) hn), a,
    hA.out out (.inl ho) hn' (by unfold oT oM; omega_using [fit]) (by omega_using [q2]), ha, e⟩

theorem pow_R57 {o a b X i j q N : Nat} (hodd : N % 2 = 1) (ha : a % N = X ^ i * R57 q % N)
    (hb : b % N = X ^ j * R57 q % N) (h : o * R57 q % N = a * b % N) : o % N = X ^ (i + j) * R57 q % N :=
  mont_pow (VG.Proof.Bignum.coprime_pow2 hodd (513 * q)) ha hb h

theorem outAT_low {B : Addr} {w q : Nat} {m m' : Mem} (hw : w = 8 * q) (h : OutAT B q (oM q (slot w 0)) m m') : Low B w m m' :=
  Low.of_out hw h (by unfold oA; omega_using []) (by unfold oA; omega_using [])

/-- A square of `A`. -/
theorem sqr57_run {t₀ u : State} {B : Addr} {Z w N q X RR c : Nat} (hw : w = 8 * q) (q2 : 2 ≤ q) (q6 : q ≤ 6) (hodd : N % 2 = 1)
    (h : Run57 t₀ u B Z w N q X RR c) :
    WP isa sqrOp57 u fun t => Run57 t₀ t B Z w N q X RR (c + c) ∧ Keep opRegs u t := by
  obtain ⟨a, hA, ha, e⟩ := h.acc
  refine WP.mono (sqrOp57_ok (h.ctx.sp hw q2 q6) h.mod hA ha) fun t ⟨⟨_, t0, mt, ot, o, hO, lo, eo, _⟩, k⟩ => ⟨⟨?_, mt, ?_, o, hO, lo, fun hE => ?_⟩, k⟩
  · exact h.ctx.op hw k t0 (outAT_low hw ot)
  · exact Mont.Outside.trans h.low (outAT_low hw ot)
  · exact pow_R57 hodd (e hE) (e hE) eo

/-- A product of `A` by `E`, unpacked from array 5. -/
theorem mul57_run {t₀ u : State} {B : Addr} {Z w N q X RR c d : Nat} (hw : w = 8 * q) (q2 : 2 ≤ q) (q6 : q ≤ 6)
    (h : Run57 t₀ u B Z w N q X RR c) (h5 : A u.mem B w 5 = d) (hd : d < 2 * N) :
    WP isa mulE u fun t => (WCtx t B Z w N ∧ Mod57 t B q (slot w 0) N ∧ Low B w t₀.mem t.mem ∧
      ∃ a o, AIn t.mem B q (oM q (slot w 0)) o ∧ o < 2 * N ∧ o * R57 q % N = a * d % N ∧
        (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → a % N = X ^ c * R57 q % N) ∧ (d ≤ 1 → o ≤ N)) ∧ Keep opRegs u t := by
  obtain sp := h.ctx.sp hw q2 q6
  obtain fit := sp.fit
  obtain d8 := sp.d8
  have hn := h.ctx.scr.nowrap
  unfold mulE
  refine WP.seq (WP.mono (unpackFrom_ok (dD := oE q (oM q (slot w 0))) sp (fun u hu h2 => atE_ok hu h2) (by unfold oE oM; omega_using [fit])
    (by unfold oE oM; omega_using [d8]) (.inl (by unfold oE oM o5; omega_using [q2]))) fun v ⟨⟨m₁, o1, o2, lE, eE⟩, kv⟩ => ?_)
  obtain ov : Mont.Outside B (o5 q (slot w 0) + 64 * q) (oE q (oM q (slot w 0)) + 72 * q - (o5 q (slot w 0) + 64 * q)) u.mem v.mem :=
    Mont.Outside.trans (o1.mono (Nat.le_refl _) (by unfold oE oM o5; omega_using [q2]))
      (o2.mono (by unfold oE oM o5; omega_using [q2]) (by unfold oE oM o5; omega_using [q2]))
  obtain t0 : v.gpr .t0 = BitVec.ofNat 64 (8 * q) := by rw [kv.gpr (by decide), h.ctx.t0, hw]
  obtain cv := h.ctx.op hw (kv.mono (rs' := opRegs) (by decide)) t0
    (Low.of_out hw ov (by unfold oM o5; omega_using []) (by unfold oE oM o5; omega_using [q2]))
  obtain hv := h.of hw q2 q6 cv kv (by decide) ov (by unfold oT oM o5; omega_using [q2]) (by unfold oE oM o5; omega_using [q2])
  rw [show 8 * q = w from hw.symm, show o5 q (slot w 0) = slot w 5 from (slot5 hw).symm, show wordsVal u.mem B (slot w 5) w = d from h5] at eE
  obtain ⟨a, hA, ha, e⟩ := hv.acc
  refine WP.mono (mulOp57_ok (cv.sp hw q2 q6) hv.mod hA ha lE eE hd) fun t ⟨⟨_, t0', mt, ot, o, hO, lo, eo, l1⟩, k⟩ =>
    ⟨⟨?_, mt, ?_, a, o, hO, lo, eo, e, l1⟩, Keep.trans' (kv.mono (rs' := opRegs) (by decide)) (k.mono (by decide))⟩
  · exact cv.op hw k t0' (outAT_low hw ot)
  · exact Mont.Outside.trans hv.low (outAT_low hw ot)

/-- `init57`. -/
theorem init57_ok {s : State} {B : Addr} {Z w N q X RR : Nat} (h : WCtx s B Z w N) (hw : w = 8 * q) (q2 : 2 ≤ q) (q6 : q ≤ 6)
    (hN : 0 < N) (htab : Tab57 s.mem B w q N X RR 16) :
    WP isa init57 s fun t => Run57 s t B Z w N q X RR 0 ∧ Keep (opRegs ++ copyRegs) s t := by
  obtain sp := h.sp hw q2 q6
  obtain fit := sp.fit
  obtain d8 := sp.d8
  have hn := h.scr.nowrap
  have hn' := h.nw
  unfold init57
  refine WP.seq (WP.mono (pads_ok sp) fun s₁ ⟨⟨o1, pM, pA⟩, k1⟩ => ?_)
  obtain l1 : Low B w s.mem s₁.mem := Low.of_out hw o1 (Nat.le_refl _) (by omega_using [])
  obtain c1 := h.of k1 (by decide) l1.win
  -- `M`.
  refine WP.seq (WP.mono (copy_ok c1 (o := 5) (a := 0) (by decide) (by decide) (by decide)) fun s₂ ⟨⟨v2, o2⟩, k2⟩ => ?_)
  replace o2 : Mont.Outside B (slot w 5) (8 * w) s₁.mem s₂.mem := o2
  obtain c2 := c1.of k2 (by decide) (Low.of5 o2).win
  rw [show A s₁.mem B w 0 = N from c1.n] at v2
  obtain sp2 := c2.sp hw q2 q6
  refine WP.seq (WP.mono (unpackFrom_ok (dD := oM q (slot w 0)) sp2 (fun u hu _ => atM_ok hu) (by unfold oM; omega_using [fit])
    (by unfold oM; omega_using [d8]) (.inr (by unfold oM o5; omega_using []))) fun s₃ ⟨⟨m₁, p1, p2, lM, eM⟩, k3⟩ => ?_)
  rw [show 8 * q = w from hw.symm, show o5 q (slot w 0) = slot w 5 from (slot5 hw).symm, show wordsVal s₂.mem B (slot w 5) w = N from v2] at eM
  obtain l3 : Low B w s₂.mem s₃.mem := Mont.Outside.trans (Low.of_out hw p1 (by unfold oM o5; omega_using []) (by unfold oM o5; omega_using [q2]))
    (Low.of_out hw p2 (Nat.le_refl _) (by omega_using []))
  obtain c3 := c2.of k3 (by decide) l3.win
  -- `A`.
  refine WP.seq (WP.mono (copy_ok c3 (o := 5) (a := 8) (by decide) (by decide) (by decide)) fun s₄ ⟨⟨v4, o4⟩, k4⟩ => ?_)
  replace o4 : Mont.Outside B (slot w 5) (8 * w) s₃.mem s₄.mem := o4
  obtain c4 := c3.of k4 (by decide) (Low.of5 o4).win
  obtain l13 : Low B w s.mem s₃.mem := Mont.Outside.trans (Mont.Outside.trans l1 (Low.of5 o2)) l3
  rw [l13.arr (by decide) (.inr (Nat.le_refl _)) hn'] at v4
  obtain sp4 := c4.sp hw q2 q6
  refine WP.mono (unpackFrom_ok (dD := oA q (oM q (slot w 0))) sp4 (fun u hu h2 => atA_ok hu h2) (by unfold oA oM; omega_using [fit])
    (by unfold oA oM; omega_using [d8]) (.inr (by unfold oA oM o5; omega_using []))) fun s₅ ⟨⟨m₂, p3, p4, lA, eA⟩, k5⟩ => ?_
  rw [show 8 * q = w from hw.symm, show o5 q (slot w 0) = slot w 5 from (slot5 hw).symm,
    show wordsVal s₄.mem B (slot w 5) w = A s.mem B w 8 from v4] at eA
  obtain l5 : Low B w s₄.mem s₅.mem := Mont.Outside.trans (Low.of_out hw p3 (by unfold oM o5; omega_using []) (by unfold oM o5; omega_using [q2]))
    (Low.of_out hw p4 (by unfold oA; omega_using []) (by unfold oA; omega_using []))
  obtain c5 := c4.of k5 (by decide) l5.win
  obtain K := (((k1.trans k2).trans k3).trans k4).trans k5
  -- What the later steps keep of `M` and the paddings.
  rw [slot5 hw] at o2 o4
  obtain k35 : ∀ {d k : Nat}, d + 8 * k ≤ oA q (oM q (slot w 0)) → lv s₅.mem B d k = lv s₃.mem B d k := fun {d k} hd => by
    rw [p4.lv (.inl hd) (by unfold oA oM at hd; omega_using [hd, fit, hn]), p3.lv (.inl (by unfold oA oM at hd; unfold o5; omega_using [hd])) (by unfold oA oM at hd; omega_using [hd, fit, hn]),
      o4.lv (.inl (by unfold oA oM at hd; unfold o5; omega_using [hd])) (by unfold oA oM at hd; omega_using [hd, fit, hn])]
  obtain k13 : ∀ {d k : Nat}, oM q (slot w 0) + 72 * q ≤ d → d + 8 * k ≤ o5 q (slot w 0) → lv s₃.mem B d k = lv s₁.mem B d k := fun {d k} hd hd' => by
    rw [p2.lv (.inr hd) (by unfold o5 at hd'; omega_using [hd', fit, hn]), p1.lv (.inl (by omega_using [hd'])) (by unfold o5 at hd'; omega_using [hd', fit, hn]),
      o2.lv (.inl hd') (by unfold o5 at hd'; omega_using [hd', fit, hn])]
  obtain hlt : A s.mem B w 8 < N := (htab 0 (by decide)).1
  refine ⟨⟨c5, ⟨⟨?_, ?_, ?_, ?_⟩, hN, ?_⟩, ?_, A s.mem B w 8, ⟨eA, lA, ?_⟩, ?_, ?_⟩, K.mono (by decide)⟩
  · rw [k35 (by unfold oA; omega_using [])]; exact eM
  · refine p4.lim (.inl (by unfold oA; omega_using [])) (by unfold oM; omega_using [fit, hn]) (p3.lim (.inl (by unfold oM o5; omega_using []))
      (by unfold oM; omega_using [fit, hn]) (o4.lim (.inl (by unfold oM o5; omega_using [])) (by unfold oM; omega_using [fit, hn]) lM))
  · rw [k35 (by unfold oA; omega_using []), k13 (Nat.le_refl _) (by unfold oM o5; omega_using [])]; exact pM
  · -- The inverse: the first limb is the first word modulo `2⁵⁷`.
    obtain inv := c5.inv
    obtain w0 : (Mont.word s₅.mem B (oM q (slot w 0))).toNat % 2 ^ 57 = (Mont.word s₅.mem B (slot w 0)).toNat % 2 ^ 57 := by
      obtain e1 : lv s₅.mem B (oM q (slot w 0)) (9 * q) = N := by rw [k35 (by unfold oA; omega_using [])]; exact eM
      obtain e2 : wordsVal s₅.mem B (slot w 0) (w - 1 + 1) = N := by
        rw [Nat.sub_add_cancel (by omega_using [hw, q2])]; exact c5.n
      rw [show 9 * q = 1 + (9 * q - 1) by omega_using [q2], lv_append, lv_one] at e1
      rw [wordsVal] at e2
      omega_using [e1, e2]
    rw [Nat.add_mod, Nat.mul_mod, w0, ← Nat.mul_mod, ← Nat.add_mod]
    omega_using [inv]
  · rw [← h.n, hw, show 512 * q = 64 * (8 * q) by omega_using []]; exact wordsVal_lt _ _ _ _
  · exact Mont.Outside.trans (Mont.Outside.trans l13 (Low.of5 (by rw [slot5 hw]; exact o4))) l5
  · rw [p4.lv (.inr (Nat.le_refl _)) (by unfold oA oM; omega_using [fit, hn]), p3.lv (.inl (by unfold oA oM o5; omega_using [])) (by unfold oA oM; omega_using [fit, hn]),
      o4.lv (.inl (by unfold oA oM o5; omega_using [])) (by unfold oA oM; omega_using [fit, hn]), k13 (by unfold oA; omega_using []) (by unfold oA oM o5; omega_using [])]
    exact pA
  · omega_using [hlt]
  · exact (htab 0 (by decide)).2

/-- The exponent of the windows so far, of the bytes at `D`. -/
def pre57 (m : Mem) (D : Addr) (j : Nat) : Nat :=
  if j % 2 = 0 then Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D (j / 2))
  else 16 * Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D (j / 2)) + (m (Mont.off D (j / 2))).toNat / 16

/-- Window `j`'s digit. -/
def dig57 (m : Mem) (D : Addr) (j : Nat) : Nat :=
  if j % 2 = 0 then (m (Mont.off D (j / 2))).toNat / 16 else (m (Mont.off D (j / 2))).toNat % 16

theorem pre57_succ (m : Mem) (D : Addr) (j : Nat) : pre57 m D (j + 1) = 16 * pre57 m D j + dig57 m D j := by
  unfold pre57 dig57
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [ite_eq_right (by omega_using [h]), ite_eq_left h, ite_eq_left h, show (j + 1) / 2 = j / 2 by omega_using [h]]
  · rw [ite_eq_left (by omega_using [h]), ite_eq_right (by omega_using [h]), ite_eq_right (by omega_using [h]),
      show (j + 1) / 2 = j / 2 + 1 by omega_using [h], Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc]
    omega_using []

theorem dig57_lt (m : Mem) (D : Addr) (j : Nat) : dig57 m D j < 16 := by
  have := (m (Mont.off D (j / 2))).isLt
  unfold dig57
  split <;> omega_using [this]

theorem and1 (n : Nat) (h : n < 2 ^ 64) : BitVec.ofNat 64 n &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  obtain e := Nat.and_two_pow_sub_one_eq_mod n 1
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at e ⊢
  rw [e]
  omega_using []

theorem and3 (n : Nat) (h : n < 2 ^ 64) : BitVec.ofNat 64 n &&& BitVec.ofNat 64 3 = BitVec.ofNat 64 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  obtain e := Nat.and_two_pow_sub_one_eq_mod n 2
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at e ⊢
  rw [e]
  omega_using []

theorem nib57 (b : BitVec 8) : ((BitVec.ofNat 64 b.toNat) &&& BitVec.ofNat 64 15) = BitVec.ofNat 64 (b.toNat % 16) ∧
    ((BitVec.ofNat 64 b.toNat) >>> 4 &&& BitVec.ofNat 64 15) = BitVec.ofNat 64 (b.toNat / 16) := by
  have hb := b.isLt
  obtain a : ∀ n < 256, BitVec.ofNat 64 n &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (n % 16) := fun n hn => by
    apply BitVec.eq_of_toNat_eq
    obtain e := Nat.and_two_pow_sub_one_eq_mod n 4
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
    simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at e ⊢
    rw [e]
    omega_using []
  refine ⟨a _ hb, ?_⟩
  rw [srl_ofNat (by omega_using [hb]), a _ (by omega_using [hb])]
  exact congrArg _ (by omega_using [hb])

/-- `digit`: window `j`'s digit, with `s10 = 4 m`, `m` the windows after it, of `2 L`. -/
theorem digit_ok {u : State} {D : Addr} {j m L : Nat} (hm : j + 1 + m = 2 * L) (hL : L < 2 ^ 32)
    (h9 : u.gpr .s9 = Mont.off D (j / 2)) (h10 : u.gpr .s10 = BitVec.ofNat 64 (4 * m))
    (hrd : InRegions (u.rd ++ u.wr) (Mont.off D (j / 2)) 1) :
    WP isa (.block digit) u fun t => (t.gpr .t6 = BitVec.ofNat 64 (dig57 u.mem D j) ∧ t.gpr .s9 = Mont.off D ((j + 1) / 2) ∧
      t.mem = u.mem) ∧ Keep [.t6, .t2, .s0, .s9] u t := by
  obtain e1 : BitVec.ofNat 64 (4 * m) >>> 2 &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (m % 2) := by
    rw [srl_ofNat (by omega_using [hm, hL]), and1 _ (by omega_using [hm, hL])]; exact congrArg _ (by omega_using [])
  generalize hb : u.mem (Mont.off D (j / 2)) = b
  obtain ⟨n1, n2⟩ := nib57 b
  unfold digit dig57
  rw [hb]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · obtain m1 : m % 2 = 1 := by omega_using [hm, h]
    rw [m1] at e1
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h9, h10, hrd, read_byte64, hb, e1, ↓exec_srlReg', n1, n2, add_ofNat_zero, h,
      show (BitVec.ofNat 64 1 <<< 2).toNat % 64 = 4 from rfl,
      show BitVec.ofNat 64 1 ^^^ BitVec.ofNat 64 1 = BitVec.ofNat 64 0 from rfl,
      show (j + 1) / 2 = j / 2 by omega_using [h]]
  · obtain m1 : m % 2 = 0 := by omega_using [hm, h]
    rw [m1] at e1
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h9, h10, hrd, read_byte64, hb, e1, ↓exec_srlReg', n1, n2, add_ofNat_zero, h,
      show (BitVec.ofNat 64 0 <<< 2).toNat % 64 = 0 from rfl, BitVec.ushiftRight_zero,
      show BitVec.ofNat 64 0 ^^^ BitVec.ofNat 64 1 = BitVec.ofNat 64 1 from rfl,
      show (j + 1) / 2 = j / 2 + 1 by omega_using [h]]

theorem Low.read {B D : Addr} {Z w L i : Nat} {m m' : Mem} (h : Low B w m m') (hZ : slot w 24 ≤ Z)
    (hsep : ∀ i < L, ∀ x, VG.Proof.Bignum.ofs B x < Z → Mont.off D i ≠ x) (hi : i < L) : m' (Mont.off D i) = m (Mont.off D i) := by
  refine h _ ?_
  have := slot_lt (w := w) (show 2 < 24 by decide)
  right
  by_contra hc
  refine hsep i hi (Mont.off D i) ?_ rfl
  simp only [VG.Proof.Bignum.ofs, Mont.ofs] at hc ⊢
  unfold slot at hc hZ
  omega_using [hc, hZ]

/-- The registers a window writes. -/
def win57Regs : List Reg := opRegs ++ WinSelect.RISCV64.selectRegs ++ [.s9, .s10]

/-- `window57`: window `j` of `2 L`, `m` after it. -/
theorem window57_ok {t₀ u : State} {B D : Addr} {Z w N q X RR c j m L : Nat} (hw : w = 8 * q) (q2 : 2 ≤ q) (q6 : q ≤ 6)
    (hodd : N % 2 = 1) (htab : Tab57 t₀.mem B w q N X RR 16) (h : Run57 t₀ u B Z w N q X RR c)
    (hm : j + 1 + m = 2 * L) (hL : L < 2 ^ 32) (h9 : u.gpr .s9 = Mont.off D (j / 2))
    (h10 : u.gpr .s10 = BitVec.ofNat 64 (4 * (m + 1))) (hrd : InRegions (u.rd ++ u.wr) (Mont.off D (j / 2)) 1)
    (hsep : ∀ i < L, ∀ x, VG.Proof.Bignum.ofs B x < Z → Mont.off D i ≠ x) :
    WP isa window57 u fun t => Run57 t₀ t B Z w N q X RR (16 * c + dig57 t₀.mem D j) ∧
      t.gpr .s9 = Mont.off D ((j + 1) / 2) ∧ t.gpr .s10 = BitVec.ofNat 64 (4 * m) ∧ Keep win57Regs u t := by
  have hn := h.ctx.nw
  unfold window57
  -- The squares.
  refine WP.seq (WP.mono (count_loop (cr := .t2) (n := 4) (by decide) (fun k t => Run57 t₀ t B Z w N q X RR (2 ^ k * c) ∧
      t.gpr .s10 = BitVec.ofNat 64 (4 * (m + 1) - k) ∧ Keep (opRegs ++ ([.s10] : List Reg)) u t) (fun k hk t ⟨ht, t10, kt⟩ => ?_)
      ⟨by rw [Nat.pow_zero, Nat.one_mul]; exact h, h10, Keep.refl _ _⟩) fun s₁ ⟨h1, x10, k1⟩ => ?_)
  · refine WP.seq (WP.mono (sqr57_run hw q2 q6 hodd ht) fun v ⟨hv, kv⟩ => ?_)
    obtain v10 : v.gpr .s10 = BitVec.ofNat 64 (4 * (m + 1) - k) := (kv.gpr (by decide)).trans t10
    obtain r : WP isa (.block [.addi .s10 .s10 (-1), .logicImm .and .t2 .s10 3]) v fun t =>
        (t.gpr .s10 = BitVec.ofNat 64 (4 * (m + 1) - (k + 1)) ∧ t.gpr .t2 = BitVec.ofNat 64 ((4 * (m + 1) - (k + 1)) % 4) ∧ t.mem = v.mem) ∧
          Keep [.s10, .t2] v t := by
      obtain e : BitVec.ofNat 64 (4 * (m + 1) - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (4 * (m + 1) - (k + 1)) := by
        rw [sub_ofNat (by omega_using [hk])]; exact congrArg _ (by omega_using [])
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [v10, e, and3 (4 * (m + 1) - (k + 1)) (by omega_using [hm, hL])]
    refine WP.mono r fun t ⟨⟨t10', t2, tm⟩, kt'⟩ => ⟨⟨?_, t10', Keep.trans' kt ((kv.trans kt').mono (by decide))⟩, ?_⟩
    · rw [show 2 ^ (k + 1) * c = 2 ^ k * c + 2 ^ k * c by rw [Nat.pow_succ, Nat.mul_two, Nat.add_mul]]
      obtain ⟨a, hA, ha, e⟩ := hv.acc
      refine ⟨hv.ctx.regs kt' (by decide) tm, ⟨⟨by rw [tm]; exact hv.mod.mod.val, by rw [tm]; exact hv.mod.mod.lim,
        by rw [tm]; exact hv.mod.mod.pad, by rw [tm, kt'.gpr (by decide)]; exact hv.mod.mod.inv⟩, hv.mod.pos, hv.mod.lt⟩,
        by rw [tm]; exact hv.low, a, by rw [tm]; exact hA, ha, e⟩
    · rw [t2, BitVec.toNat_ofNat]
      omega_using [hk]
  -- The digit.
  rw [show 4 * (m + 1) - 4 = 4 * m by omega_using []] at x10
  refine WP.seq (WP.mono (digit_ok hm hL ((k1.gpr (by decide)).trans h9) x10 (by rw [k1.2.1, k1.2.2]; exact hrd))
    fun s₂ ⟨⟨y6, y9, m2⟩, k2⟩ => ?_)
  obtain eb : dig57 s₁.mem D j = dig57 t₀.mem D j := by
    unfold dig57
    rw [h1.low.read h.ctx.hZ hsep (show j / 2 < L by omega_using [hm])]
  rw [eb] at y6
  obtain hd := dig57_lt t₀.mem D j
  generalize dig57 t₀.mem D j = d at y6 hd
  obtain c2 := h1.ctx.regs k2 (by decide) m2
  -- The entry.
  refine WP.seq (WP.mono (WinSelect.RISCV64.winSelect_ok (o := 5) (t := 8) c2.scr c2.a7 c2.s5 c2.t0 (by have := c2.w2; omega_using [this]) c2.w31 y6 hd
    (by decide) c2.hZ) fun s₃ ⟨⟨z5, o3⟩, k3⟩ => ?_)
  rw [m2] at z5 o3
  obtain o3' : Mont.Outside B (slot w 5) (8 * (w + 2)) s₁.mem s₃.mem := fun x hx => o3 x fun j hj => by
    obtain rfl : j = 5 := by simpa using hj
    exact hx
  obtain k23 := k2.trans k3
  obtain c3 := h1.ctx.of k23 (by decide) (Low.of_arr o3 (by decide) (by decide)).win
  obtain h3 := h1.of hw q2 q6 c3 k23 (by decide) o3' (by rw [slot5 hw]; unfold oT oM o5; omega_using [q2])
    (by rw [slot5 hw]; unfold oM o5; omega_using [hw])
  obtain ⟨td, te⟩ := htab d hd
  obtain z5' : A s₃.mem B w 5 = A t₀.mem B w (8 + d) :=
    Eq.trans z5 (h1.low.arr (by omega_using [hd]) (.inr (by omega_using [])) hn)
  -- The product.
  refine WP.mono (mul57_run hw q2 q6 h3 z5' (by omega_using [td])) fun t ⟨⟨ct, mt, lt, a, o, hO, lo, eo, ea, _⟩, k4⟩ => ⟨⟨ct, mt, lt, o, hO, lo, fun hE => ?_⟩, ?_, ?_, ?_⟩
  · exact pow_R57 hodd (ea hE) (te hE) eo
  · rw [k4.gpr (by decide), k3.gpr (by decide), y9]
  · rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), x10]
  · exact ((k1.trans k23).trans k4).mono (by decide)

/-- `exit57`: `A R'⁻¹ mod m` into array 4. -/
theorem exit57_ok {t₀ u : State} {B : Addr} {Z w N q X RR c : Nat} (hw : w = 8 * q) (q2 : 2 ≤ q) (q6 : q ≤ 6)
    (hN : 2 ≤ N) (hodd : N % 2 = 1) (h : Run57 t₀ u B Z w N q X RR c) (hRR : A t₀.mem B w 1 = RR) (hlt : RR < N) :
    WP isa exit57 u fun t => ((RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A t.mem B w 4 = X ^ c % N) ∧
      WinO B w t₀.mem t.mem ∧ A t.mem B w 1 = RR ∧ t.gpr .t0 = BitVec.ofNat 64 w) ∧ Keep (opRegs ++ copyRegs ++ Pub.montRegs) u t := by
  have hn := h.ctx.nw
  have hw2 := h.ctx.w2
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold exit57
  -- 1 into array 5.
  refine WP.seq (WP.mono (Pub.oneP_ok h.ctx.scr (by omega_using [hw2]) h.ctx.w31
    (Nat.le_trans (by unfold slot; omega_arith) h.ctx.hZ) h.ctx.a7 h.ctx.s5 h.ctx.t0) fun s₁ ⟨⟨v1, o1⟩, k1⟩ => ?_)
  replace v1 : A s₁.mem B w 7 = 1 := v1
  replace o1 : Mont.Outside B (slot w 7) (8 * w) u.mem s₁.mem := o1
  obtain c1 := h.ctx.of k1 (by decide) (arrO o1 (by decide) (by decide))
  obtain e7 : slot w 7 = oM q (slot w 0) + 320 * q + 80 := by rw [slot_at hw]; unfold oM; omega_using []
  obtain h1 := h.of hw q2 q6 c1 k1 (by decide) o1 (by rw [e7]; unfold oT; omega_using [q2]) (by rw [e7]; omega_using [hw])
  refine WP.seq (WP.mono (copy_ok c1 (o := 5) (a := 7) (by decide) (by decide) (by decide)) fun s₂ ⟨⟨v2, o2⟩, k2⟩ => ?_)
  replace o2 : Mont.Outside B (slot w 5) (8 * w) s₁.mem s₂.mem := o2
  obtain c2 := c1.of k2 (by decide) (Low.of5 o2).win
  obtain h2 := h1.of hw q2 q6 c2 k2 (by decide) o2 (by rw [slot5 hw]; unfold oT oM o5; omega_using [q2])
    (by rw [slot5 hw]; unfold oM o5; omega_using [hw])
  rw [v1] at v2
  refine WP.seq (WP.mono (mul57_run hw q2 q6 h2 v2 (by omega_using [hN])) fun s₃ ⟨⟨c3, _, l3, a, o, hO, lo, eo, ea, lo1⟩, k3⟩ => ?_)
  obtain lo1 := lo1 (Nat.le_refl 1)
  -- Out of radix `2⁵⁷`.
  refine WP.seq (WP.mono (pack_ok (c3.sp hw q2 q6) (by rw [c3.t0, hw]) hO) fun s₄ ⟨⟨o4, v4⟩, k4⟩ => ?_)
  obtain c4 := c3.of k4 (by decide) (Low.win (Low.of_out hw o4 (by unfold oM o6; omega_using []) (by unfold oM o6; omega_using [q2])))
  obtain l4 : Low B w t₀.mem s₄.mem := Mont.Outside.trans l3 (Low.of_out hw o4 (by unfold oM o6; omega_using []) (by unfold oM o6; omega_using [q2]))
  obtain oN : o < 2 ^ (64 * w) := by
    obtain l := wordsVal_lt s₃.mem B (slot w 0) w
    rw [show wordsVal s₃.mem B (slot w 0) w = N from c3.n] at l
    omega_using [l, lo1]
  rw [show 8 * q = w from hw.symm, show o6 q (slot w 0) = slot w 6 from (slot6 hw).symm, Nat.mod_eq_of_lt oN] at v4
  refine WP.seq (WP.mono (Pub.oneP_ok c4.scr (by omega_using [hw2]) c4.w31
    (Nat.le_trans (by unfold slot; omega_arith) c4.hZ) c4.a7 c4.s5 c4.t0) fun s₅ ⟨⟨v5, o5⟩, k5⟩ => ?_)
  replace v5 : A s₅.mem B w 7 = 1 := v5
  obtain c5 := c4.of k5 (by decide) (arrO o5 (by decide) (by decide))
  obtain R5 : A s₅.mem B w 1 = RR := by
    rw [arr_out o5 (by decide) (by decide) hn, l4.arr (by decide) (.inl (by decide)) hn, hRR]
  obtain V6 : A s₅.mem B w 6 = o := by rw [arr_out o5 (by decide) (by decide) hn]; exact v4
  -- `o R mod m`, then `o mod m`.
  refine WP.seq (WP.mono (c5.mont (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R5]; exact hlt)) fun s₆ ⟨⟨c6, lt6, e6, v6, o6⟩, k6⟩ => ?_)
  rw [V6, R5] at e6
  refine WP.mono (c6.mont (o := 4) (a := 7) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) lt6) fun t ⟨⟨c7, lt7, e7', v7, o7⟩, k7⟩ => ⟨⟨fun hE => ?_, ?_, ?_, c7.t0⟩, ?_⟩
  · rw [v6 7 (by decide) (by decide) (by decide) (by decide), v5, Nat.one_mul] at e7'
    obtain f1 : A s₆.mem B w 6 % N = o * 2 ^ (64 * w) % N := by
      refine VG.Proof.Bignum.mont_cancel hR ?_
      rw [e6, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
    obtain f2 : A t.mem B w 4 % N = o % N := VG.Proof.Bignum.mont_cancel hR (by rw [e7', f1])
    obtain f3 : o % N = X ^ c % N := by
      refine VG.Proof.Bignum.mont_cancel (VG.Proof.Bignum.coprime_pow2 hodd (513 * q)) ?_
      rw [eo, Nat.mul_one, ea hE]
    rw [← f3, ← f2, Nat.mod_eq_of_lt lt7]
  · exact ((l4.win.trans (arrO o5 (by decide) (by decide))).trans o6).trans o7
  · rw [v7 1 (by decide) (by decide) (by decide) (by decide), v6 1 (by decide) (by decide) (by decide) (by decide), R5]
  · exact ((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).mono (by decide)

/-- `powWin57`, which is `powWin` for `w = 8 q`, `2 ≤ q ≤ 6`, and fewer than `2³²` bytes of exponent. -/
theorem powWin57_ok {s : State} {B D : Addr} {Z w L q : Nat} (hs : Scr s B Z) (hw : w = 8 * q) (q2 : 2 ≤ q) (q6 : q ≤ 6)
    (hZ : slot w 24 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hN : 2 ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1)
    (hRRlt : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w)
    (h9 : s.gpr .s9 = off D 0) (h10 : s.gpr .s10 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 32)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, VG.Proof.Bignum.ofs B x < Z → off D i ≠ x) :
    WP isa powWin57 s fun t =>
      ((wordsVal s.mem B (slot w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w →
          wordsVal t.mem B (slot w 4) w =
            wordsVal s.mem B (slot w 4) w ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) %
              wordsVal s.mem B (slot w 0) w) ∧
        WinO B w s.mem t.mem ∧ wordsVal t.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w) ∧
      Keep powWRegs s t := by
  obtain h0 : WCtx s B Z w (A s.mem B w 0) := ⟨hs, by omega_using [hw, q2], by omega_using [hw, q6], hZ, h7, h5, ht0, hinv, rfl⟩
  have hn := h0.nw
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd hRRlt ⊢
  replace h0 : WCtx s B Z w N := hNd ▸ h0
  generalize hXd : wordsVal s.mem B (slot w 4) w = X
  generalize hRRd : wordsVal s.mem B (slot w 1) w = RR at hRRlt ⊢
  unfold powWin57
  refine WP.seq (WP.mono (table57_ok h0 hw q6 hodd (by rw [show A s.mem B w 1 = RR from hRRd]; exact hRRlt))
    fun t₀ ⟨⟨c0, o0, t01, htab⟩, k0⟩ => ?_)
  rw [show A s.mem B w 4 = X from hXd, show A s.mem B w 1 = RR from hRRd] at htab
  rw [show A s.mem B w 1 = RR from hRRd] at t01
  refine WP.seq (WP.mono (init57_ok c0 hw q2 q6 (by omega_using [hN]) htab) fun s₁ ⟨r1, k1⟩ => ?_)
  obtain e10 : BitVec.ofNat 64 L <<< 3 = BitVec.ofNat 64 (4 * (2 * L)) := by
    rw [sll_ofNat]; exact congrArg _ (by omega_using [])
  obtain k01 := k0.trans k1
  refine WP.seq (WP.mono (WP.keep [.s10] (Q := fun t => t.gpr .s10 = BitVec.ofNat 64 (4 * (2 * L)) ∧ t.mem = s₁.mem)
    (by brun [(k01.gpr (r := .s10) (by decide)).trans h10, e10]) (by rfl) (by rfl)) fun s₂ ⟨⟨x10, m2⟩, k2⟩ => ?_)
  obtain k02 := k01.trans k2
  obtain r2 : Run57 t₀ s₂ B Z w N q X RR (pre57 t₀.mem D 0) := by
    obtain ⟨a, hA, ha, e⟩ := r1.acc
    refine ⟨r1.ctx.regs k2 (by decide) m2, ⟨⟨by rw [m2]; exact r1.mod.mod.val, by rw [m2]; exact r1.mod.mod.lim,
      by rw [m2]; exact r1.mod.mod.pad, by rw [m2, k2.gpr (by decide)]; exact r1.mod.mod.inv⟩, r1.mod.pos, r1.mod.lt⟩,
      by rw [m2]; exact r1.low, a, by rw [m2]; exact hA, ha, fun hE => ?_⟩
    rw [e hE]
    rfl
  obtain rdb : ∀ i < L, t₀.mem (Mont.off D i) = s.mem (Mont.off D i) := fun i hi => by
    refine o0 _ ?_
    obtain e24 := slot24 w
    right
    by_contra hc
    exact hsep i hi (Mont.off D i) (by simp only [VG.Proof.Bignum.ofs] at hc ⊢; omega_using [hc, e24, hZ]) rfl
  obtain ep : pre57 t₀.mem D (2 * L) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) := by
    unfold pre57
    rw [ite_eq_left (by omega_using []), Nat.mul_div_cancel_left _ (by decide)]
    refine congrArg Spec.Rsa.os2ip ?_
    unfold Spec.Rsa.bytesAt
    exact List.map_congr_left fun i hi => rdb i (List.mem_range.mp hi)
  -- The windows.
  refine WP.seq (WP.mono (count_loop (cr := .s10) (n := 2 * L) (by omega_using [hL]) (fun j t => Run57 t₀ t B Z w N q X RR (pre57 t₀.mem D j) ∧
      t.gpr .s9 = Mont.off D (j / 2) ∧ t.gpr .s10 = BitVec.ofNat 64 (4 * (2 * L - j)) ∧ Keep (powWRegs ++ ([.t0] : List Reg)) s t)
    (fun j hj t ⟨ht, t9, t10, kt⟩ => ?_)
    ⟨r2, by rw [k02.gpr (by decide), h9], x10, k02.mono (by decide)⟩) fun u ⟨hu, _, _, ku⟩ => ?_)
  · obtain ⟨m, hm⟩ : ∃ m, j + 1 + m = 2 * L := Nat.exists_eq_add_of_le hj |>.imp fun _ h => h.symm
    refine WP.mono (window57_ok (j := j) (m := m) (L := L) hw q2 q6 hodd htab ht hm hL' t9
      (by rw [t10]; exact congrArg _ (by omega_using [hm])) (by rw [kt.2.1, kt.2.2]; exact hrd _ (by omega_using [hj])) hsep)
      fun v ⟨hv, v9, v10, kv⟩ => ⟨⟨by rw [pre57_succ]; exact hv, v9, by rw [v10]; exact congrArg _ (by omega_using [hm]),
        Keep.within kt kv (by decide)⟩, ?_⟩
    rw [v10, BitVec.toNat_ofNat]
    omega_using [hm, hL']
  -- Out of Montgomery form.
  refine WP.mono (exit57_ok hw q2 q6 hN hodd hu t01 hRRlt) fun t ⟨⟨e, ot, t1, t0⟩, k⟩ => ⟨⟨fun hE => ?_, ?_, t1⟩, ?_⟩
  · rw [show wordsVal t.mem B (slot w 4) w = A t.mem B w 4 from rfl, e hE, ep]
  · exact o0.trans ot
  · obtain K : Keep (powWRegs ++ ([.t0] : List Reg)) s t := Keep.within ku k (by decide)
    refine ⟨fun r hr => ?_, K.2.1, K.2.2⟩
    by_cases hr0 : r = .t0
    · subst hr0; rw [t0, ht0]
    · exact K.gpr fun hm => (List.mem_append.1 hm).elim hr fun h => hr0 (by simpa using h)

/-- `may57`: 0 only where `powWin57` may be used. -/
theorem may57_ok {s : State} {w L : Nat} (hw' : w < 2 ^ 31) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (h10 : s.gpr .s10 = BitVec.ofNat 64 L)
    (hL : L < 2 ^ 63) :
    WP isa (.block may57) s fun t => ((t.gpr .t2 = 0#64 → L < 2 ^ 32 ∧ ∃ q, w = 8 * q ∧ 2 ≤ q ∧ q ≤ 6) ∧ t.mem = s.mem) ∧
      Keep [.t2, .t3, .t4] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold may57
  brun [h0, h10, exec_li]
  intro h
  rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff] at h
  obtain ⟨⟨a, b⟩, c⟩ := h
  rw [sqr_rem8 w (by omega_using [hw'])] at a
  rw [srl_ofNat (by omega_using [hL])] at c
  obtain a' := congrArg BitVec.toNat a
  obtain c' := congrArg BitVec.toNat c
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at a' c'
  obtain b' : (BitVec.ofNat 64 w - BitVec.ofNat 64 16) < BitVec.ofNat 64 33 := by
    by_contra hc
    rw [ite_eq_right hc] at b
    exact absurd b (by decide)
  obtain b'' := BitVec.lt_def.mp b'
  rw [BitVec.toNat_sub] at b''
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at b''
  refine ⟨by omega_using [c', hL], w / 8, by omega_using [a', hw'], by omega_using [a', b'', hw'], by omega_using [a', b'', hw']⟩

/-! ## `powWin` as a function -/

/-- A call's code run from the call's entry state, which leaves `ra` as it
found it, returns. -/
private theorem callBody_wp {name : String} {body : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa body s.callEntry fun u => u.gpr .ra = s.callEntry.gpr .ra ∧ Q u) :
    WP isa (.call name body) s Q := by
  obtain ⟨t, u, he, hra, hq⟩ := h
  have hret : isa.ret s.callEntry u = some u := by
    simp only [isa, ret]; exact ite_eq_left_of_eq_true _ _ (eq_true hra)
  exact ⟨_, u, Exec.call (call_callEntry s) he hret, hq⟩

/-- `wOfSize`: `t0 := w`, from `s5 = 8 (w + 2)`. -/
theorem wOfSize_ok {s : State} {w : Nat} (hw' : w < 2 ^ 31) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block ModExp.wOfSize) s fun t => (t.gpr .t0 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.t0] s t := by
  unfold ModExp.wOfSize
  refine WP.keep [.t0] (Q := fun t => t.gpr .t0 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by
      brun [h5]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_using [hw'] : 8 * (w + 2) < 2 ^ 64), Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega_using [hw']) (by rfl) (by rfl)

/-- `powWinCall`: `powWin1_ok` for the call of `powWin`, which computes `t0`
and `t1` again: the same, and `ra` written. -/
theorem powWinCall_ok {name : String} {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 24 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hN : 2 ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1)
    (hRRlt : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w)
    (h9 : s.gpr .s9 = off D 0) (h10 : s.gpr .s10 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, VG.Proof.Bignum.ofs B x < Z → off D i ≠ x) :
    WP isa (ModExp.powWinCall name) s fun t =>
      ((wordsVal s.mem B (slot w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w →
          wordsVal t.mem B (slot w 4) w =
            wordsVal s.mem B (slot w 4) w ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) %
              wordsVal s.mem B (slot w 0) w) ∧
        WinO B w s.mem t.mem ∧ wordsVal t.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w) ∧
      Keep (powWRegs ++ ([.ra] : List Reg)) s t := by
  unfold ModExp.powWinCall
  refine callBody_wp ?_
  obtain ce : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  obtain hs₀ : Scr s.callEntry B Z := hs.congr (State.callEntry_wr s)
  obtain hlow : (Mont.word s.mem B (slot w 0)).toNat % 2 = 1 := by
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega_using [hw2]⟩
    simp only [wordsVal] at hodd
    omega_arith
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (wOfSize_ok hw' ((ce _ (by decide)).trans h5)) fun s₁ ⟨⟨a0₁, m₁⟩, k₁⟩ => ?_
  obtain hs₁ : Scr s₁ B Z := hs₀.congr k₁.2.2
  rw [WP.block_append_iff]
  refine WP.mono (minv_ok hs₁ (d := slot w 0) ((k₁.gpr (by decide)).trans ((ce _ (by decide)).trans h7))
    (slot_al w 0) (by unfold slot at hZ ⊢; omega_using [hZ, hw2])
    (by rw [m₁, State.callEntry_mem]; exact hlow)) fun s₂ ⟨⟨inv₂, m₂⟩, k₂⟩ => ?_
  rw [m₁, State.callEntry_mem] at inv₂
  obtain e1 : s₂.gpr .t1 = s.gpr .t1 := VG.Proof.Bignum.minv_unique hlow inv₂ hinv
  obtain e0 : s₂.gpr .t0 = s.gpr .t0 := by rw [k₂.gpr (by decide), a0₁, ht0]
  obtain k12' := k₁.trans k₂
  refine WP.mono (may57_ok (L := L) hw' (e0.trans ht0) (by
    rw [k12'.gpr (by decide), ce _ (by decide), h10]) hL') fun s₃ ⟨⟨hq, m₃⟩, k₃⟩ => ?_
  obtain k12 := k12'.trans k₃
  obtain hm₂ : s₃.mem = s.mem := by rw [m₃, m₂, m₁, State.callEntry_mem]
  obtain g : ∀ r, r ∉ [Reg.t0, .s0, .s1, .s2, .s3, .t1, .t2, .t3, .t4] → r ∉ linkRegs → s₃.gpr r = s.gpr r := fun r hr hl => by
    rw [k12.gpr (by simpa using hr), ce r hl]
  replace e0 : s₃.gpr .t0 = s.gpr .t0 := (k₃.gpr (by decide)).trans e0
  replace e1 : s₃.gpr .t1 = s.gpr .t1 := (k₃.gpr (by decide)).trans e1
  obtain hs₃ := (hs₁.congr k₂.2.2).congr k₃.2.2
  obtain pow : WP isa (.ite (.zero .t2) powWin57 powWin) s₃ fun t =>
      ((wordsVal s₃.mem B (slot w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % wordsVal s₃.mem B (slot w 0) w →
          wordsVal t.mem B (slot w 4) w =
            wordsVal s₃.mem B (slot w 4) w ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₃.mem D L) %
              wordsVal s₃.mem B (slot w 0) w) ∧
        WinO B w s₃.mem t.mem ∧ wordsVal t.mem B (slot w 1) w = wordsVal s₃.mem B (slot w 1) w) ∧
      Keep powWRegs s₃ t := by
    obtain a7 : s₃.gpr .a7 = off B (slot w 0) := by rw [g _ (by decide) (by decide)]; exact h7
    obtain a5 : s₃.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) := by rw [g _ (by decide) (by decide)]; exact h5
    obtain a9 : s₃.gpr .s9 = off D 0 := by rw [g _ (by decide) (by decide)]; exact h9
    obtain a10 : s₃.gpr .s10 = BitVec.ofNat 64 L := by rw [g _ (by decide) (by decide)]; exact h10
    obtain hrd' : ∀ i < L, InRegions (s₃.rd ++ s₃.wr) (off D i) 1 := fun i hi => by
      rw [k12.2.1, k12.2.2, State.callEntry_rd, State.callEntry_wr]; exact hrd i hi
    refine WP.ite _ (Steps.eval_zero _ _) (fun hz => ?_) (fun _ => ?_)
    · obtain ⟨hL32, q, hwq, q2, q6⟩ := hq (by simpa using hz)
      exact powWin57_ok hs₃ hwq q2 q6 hZ a7 a5 (e0.trans ht0) (by rw [e1, hm₂]; exact hinv) (by rw [hm₂]; exact hN)
        (by rw [hm₂]; exact hodd) (by rw [hm₂]; exact hRRlt) a9 a10 hL hL32 hrd' hsep
    · exact powWin1_ok hs₃ hw2 hw' hZ a7 a5 (e0.trans ht0) (by rw [e1, hm₂]; exact hinv) (by rw [hm₂]; exact hN)
        (by rw [hm₂]; exact hodd) (by rw [hm₂]; exact hRRlt) a9 a10 hL hL' hrd' hsep
  refine WP.mono pow
    fun t ⟨⟨hpow, hout, h1⟩, kt⟩ => ⟨?_, ?_, ?_⟩
  · rw [kt.gpr (by decide), k12.gpr (by decide)]
  · rw [hm₂] at hpow hout h1; exact ⟨hpow, hout, h1⟩
  · refine ⟨fun r hr => ?_, kt.2.1.trans (k12.2.1.trans (State.callEntry_rd s)),
      kt.2.2.trans (k12.2.2.trans (State.callEntry_wr s))⟩
    simp only [List.mem_append, List.mem_singleton, not_or] at hr
    rw [kt.gpr hr.1]
    by_cases h0 : r = .t0
    · subst h0; exact e0
    by_cases h1 : r = .t1
    · subst h1; exact e1
    have hl : r ∉ linkRegs := by
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h | h | h | h | h | h | h) <;> subst h <;> first | exact hr.2 rfl | exact h0 rfl | exact h1 rfl |
        exact hr.1 (by decide)
    exact g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h | h | h | h | h | h | h | h) <;> subst h <;> first | exact h0 rfl | exact h1 rfl | exact hr.1 (by decide)) hl

end VG.Proof.Bignum.RISCV64.Win
