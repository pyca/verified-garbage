module

-- separate module: the windowed exponentiation, the largest of the CRT's proofs, apart from `CrtR2`, which `recombineP`'s proof imports too
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontSqr
public import VerifiedGarbage.Impl.Bignum.RISCV64.ModExp
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontRounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.Math
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
`x^d mod m` in array 4.
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
  have e24 := slot24 w
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
  have s0 := slot_lt (w := w) (show 0 < 24 by decide)
  have e1 : slot w 1 = slot w 0 + 8 * (w + 2) := by unfold slot; omega_arith
  have g := fun r hr => k.gpr (r := r) (hrs r hr)
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
  have op := win_of_arrays out (by
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
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k12.gpr (by decide)).trans h.a7)
    ((k12.gpr (by decide)).trans h.s5) 2) fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k13.gpr (by decide)).trans h.a7)
    ((k13.gpr (by decide)).trans h.s5) p) fun t₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  have c4 := h.regs k14 (by decide) hm
  have g2 : t₄.gpr .a2 = off B (slot w o) := by rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), a2]
  have g3 : t₄.gpr .a3 = off B (slot w a) := by rw [k4.gpr (by decide), k3.gpr (by decide), a3]
  have g5 : t₄.gpr .a5 = off B (slot w 2) := by rw [k4.gpr (by decide), a5]
  rw [← hm] at hA ⊢
  refine WP.mono (sqrTailN_ok c4.scr (n := 24) (by decide) ho ha hp ho2 ho3 ha2 ha3 hp0 hp2 hp3 hpo c4.w2 c4.w31
    c4.hZ g2 g3 g5 a6 c4.a7 c4.t0 c4.inv (by rw [show wordsVal t₄.mem B (slot w 0) w = N from c4.n]; exact hA))
    fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  have op := win_of_arrays out (by
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
  have sep := fun {j k : Nat} (hjk : j ≠ k) => slot_sep (w := w) hjk
  have hO := h.sl ho
  have hA := h.sl ha
  have hT := h.sl ht
  have al := slot_al w
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
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k12.gpr (by decide)).trans h.a7)
    ((k12.gpr (by decide)).trans h.s5) a) fun t₃ ⟨⟨a6, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) ((k13.gpr (by decide)).trans h.a7)
    ((k13.gpr (by decide)).trans h.s5) o) fun t₄ ⟨⟨a2, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
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
  have c1 := h.regs k1 (by decide) m1
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok (j := j) c1 (.inl ⟨rfl, rfl⟩) (by rw [k1.gpr (by decide), h7]))
    fun t₂ ⟨⟨a2, m2⟩, k2⟩ => ?_
  have c2 := c1.regs k2 (by decide) m2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) c2.a7 c2.s5 6) fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have c3 := c2.regs k3 (by decide) m3
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) c3.a7 c3.s5 6) fun t₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  have c4 := c3.regs k4 (by decide) m4
  have k14 := ((k1.trans k2).trans k3).trans k4
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
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
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hX : A s.mem B w 4 = X
  generalize hRRd : A s.mem B w 1 = RR at hRR
  unfold table
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok h.scr (by have := h.w2; omega_arith) h.w31
    (Nat.le_trans (by unfold slot; omega_arith) h.hZ) h.a7 h.s5 h.t0) fun s₁ ⟨⟨h7, o1⟩, k1⟩ => ?_)
  replace h7 : A s₁.mem B w 7 = 1 := h7
  have c1 := h.of k1 (by decide) (arrO o1 (by decide) (by decide))
  have R1 : A s₁.mem B w 1 = RR := by rw [arr_out o1 (by decide) (by decide) hn, hRRd]
  have X1 : A s₁.mem B w 4 = X := by rw [arr_out o1 (by decide) (by decide) hn, hX]
  -- `T_0 = R mod m`.
  refine WP.seq (WP.mono (c1.mont (o := 8) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h7]; omega_arith)) fun s₂ ⟨⟨c2, lt2, e2, v2, o2⟩, k2⟩ => ?_)
  rw [h7, Nat.mul_one, R1] at e2
  have T0 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₂.mem B w 8 % N = X ^ 0 * 2 ^ (64 * w) % N :=
    fun hE => by
      rw [Nat.pow_zero, Nat.one_mul]
      exact VG.Proof.Bignum.mont_cancel hR (by rw [e2, hE, Nat.mod_mod])
  have R2 : A s₂.mem B w 1 = RR := by rw [v2 1 (by decide) (by decide) (by decide) (by decide), R1]
  have X2 : A s₂.mem B w 4 = X := by rw [v2 4 (by decide) (by decide) (by decide) (by decide), X1]
  have S2 : A s₂.mem B w 7 = 1 := by rw [v2 7 (by decide) (by decide) (by decide) (by decide), h7]
  -- `T_1 = x R mod m`.
  refine WP.seq (WP.mono (c2.mont (o := 9) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [R2]; exact hRR))
    fun s₃ ⟨⟨c3, lt3, e3, v3, o3⟩, k3⟩ => ?_)
  rw [X2, R2] at e3
  have T1 : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A s₃.mem B w 9 % N = X ^ 1 * 2 ^ (64 * w) % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [e3, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_one, Nat.mul_assoc]
  have R3 : A s₃.mem B w 1 = RR := by rw [v3 1 (by decide) (by decide) (by decide) (by decide), R2]
  have X3 : A s₃.mem B w 4 = X := by rw [v3 4 (by decide) (by decide) (by decide) (by decide), X2]
  have S3 : A s₃.mem B w 7 = 1 := by rw [v3 7 (by decide) (by decide) (by decide) (by decide), S2]
  have E3 : A s₃.mem B w 8 = A s₂.mem B w 8 := v3 8 (by decide) (by decide) (by decide) (by decide)
  -- `a := T_1`.
  refine WP.seq (WP.mono (copy_ok c3 (o := 6) (a := 9) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨a4, o4⟩, k4⟩ => ?_)
  have c4 := c3.of k4 (by decide) (arrO o4 (by decide) (by decide))
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = BitVec.ofNat 64 2 ∧ t.mem = s₄.mem)
    (by brun [Pub.pub_li1, exec_li]) (by rfl) (by rfl)) fun s₅ ⟨⟨a7, m5⟩, k5⟩ => ?_)
  have c5 := c4.regs k5 (by decide) m5
  have O5 : WinO B w s.mem s₅.mem := by
    rw [m5]
    exact (((arrO o1 (by decide) (by decide)).trans o2).trans o3).trans (arrO o4 (by decide) (by decide))
  have K : ∀ j, j < 24 → j ≠ 6 → A s₅.mem B w j = A s₃.mem B w j := fun j hj h6 => by
    rw [m5]; exact arr_out o4 hj h6 hn
  have tab2 : TabUpTo s₅.mem B w N X RR 2 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl
    · rw [K 8 (by decide) (by decide), E3]; exact ⟨lt2, T0⟩
    · rw [K 9 (by decide) (by decide)]; exact ⟨lt3, T1⟩
  have a5 : A s₅.mem B w 6 = A s₃.mem B w 9 := by rw [m5, a4]
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
    have cx := cu.of kx (by decide) (arrO xo (by omega_arith) (by omega_arith))
    have hend : WP isa (.block [.addi .s7 .s7 1, .addi .t2 .s7 (-16)]) x fun y =>
        (y.gpr .s7 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 ∧
          y.gpr .t2 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 - BitVec.ofNat 64 16 ∧ y.mem = x.mem) ∧
          Keep [.s7, .t2] x y := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [(kx.gpr (r := .s7) (by decide)).trans ((ku.gpr (r := .s7) (by decide)).trans t7)]
    have M : ∀ j, j < 24 → j ≠ 2 → j ≠ 3 → j ≠ 6 → j ≠ 8 + (2 + k) → A x.mem B w j = A t.mem B w j :=
      fun j hj h2 h3 h6 he => by rw [arr_out xo hj he hn, vu j hj h2 h3 h6]
    have pw : RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A u.mem B w 6 % N = X ^ (2 + k) * 2 ^ (64 * w) % N :=
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
  have hslot := slot_lt (w := w) (show 8 + j < 24 by omega_arith)
  have hfit : slot w (8 + j) + 8 * i + 8 ≤ Z := by omega_arith
  have hal : (slot w (8 + j) + 8 * i) % 8 = 0 := by
    have := slot_al w (8 + j); omega_arith
  have hm : (0#64 : BitVec 64) - ((((1#64 : BitVec 64) <<< d) >>> j) &&& 1#64) =
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
    have value : t₂.gpr .s0 = if d < n + 1 then word s.mem B (slot w (8 + d) + 8 * i) else 0#64 := by
      rw [m1, v1] at v2
      by_cases he : n = d
      · simpa [he] using v2
      · have e : (d < n) = (d < n + 1) := propext (by omega_arith)
        simpa only [he, ↓reduceIte, e] using v2
    have k12 := k1.trans k2
    have hptr2 : t₂.gpr .s1 = off B (slot w (8 + n) + 8 * i) := (k2.gpr (by decide)).trans p1
    have hhot2 : t₂.gpr .t6 = ((1#64 : BitVec 64) <<< d) >>> n := (k2.gpr (by decide)).trans b1
    have hstride2 := (k12.gpr (r := .s5) (by decide)).trans hstride
    have advance : WP isa (.block wordSelectAdvance) t₂ fun t =>
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
  have e8 : slot w 0 + 8 * (8 * (w + 2)) = slot w 8 := by unfold slot; omega_arith
  have e5 : slot w 0 + (4 * (8 * (w + 2)) + 8 * (w + 2)) = slot w 5 := by unfold slot; omega_arith
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
  have hs5 := slot_lt (w := w) (show 5 < 24 by decide)
  have hfit : slot w 5 + 8 * i + 8 ≤ Z := by omega_arith
  have hal : (slot w 5 + 8 * i) % 8 = 0 := by have := slot_al w 5; omega_arith
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
  have hs5 := slot_lt (w := w) (show 5 < 24 by decide)
  have hsd := slot_lt (w := w) (show 8 + d < 24 by omega_arith)
  have sep := slot_lt (w := w) (show 5 < 8 + d by omega_arith)
  unfold wordSelect countLoop
  refine WP.seq (WP.mono (wordSelectInit_ok h) fun t₀ ⟨⟨p0, o0, c0, m0⟩, k0⟩ => ?_)
  let I : Nat → State → Prop := fun i t =>
    WCtx t B Z w N ∧ t.gpr .t3 = off B (slot w 8 + 8 * i) ∧
      t.gpr .s4 = off B (slot w 5 + 8 * i) ∧ Outside B (slot w 5) (8 * i) s.mem t.mem ∧
      wordsVal t.mem B (slot w 5) i = wordsVal s.mem B (slot w (8 + d)) i ∧ Keep selectRegs s t
  have init : I 0 t₀ := ⟨h.regs k0 (by decide) m0, by simpa using p0, by simpa using o0,
    by rw [m0]; exact Outside.refl _ _ _ _, by simp only [wordsVal], k0.mono (by decide)⟩
  refine WP.mono (wp_countdown (cnt := .t5) (N := w) (by have := h.w31; omega_arith)
    (by have := h.w2; omega_arith) I (fun i hi t ⟨ct, pt, po, ot, vt, kt⟩ hc => ?_) init c0)
    fun t ⟨ct, _, _, ot, vt, kt⟩ => ⟨⟨vt, fun j hj _ h5 => arr_out ot hj h5 hn,
      ct, arrO ot (by decide) (by decide)⟩, kt⟩
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (wordSelectWord_ok ct.scr pt ((kt.gpr (by decide)).trans h1) ct.s5 hd hi ct.hZ)
    fun u ⟨⟨vu, mu⟩, ku⟩ => ?_
  have cu := ct.regs ku (by decide) mu
  have val_old : word t.mem B (slot w (8 + d) + 8 * i) = word s.mem B (slot w (8 + d) + 8 * i) :=
    ot.word (Or.inr (by omega_arith)) (by omega_arith)
  have val : u.gpr .s0 = word s.mem B (slot w (8 + d) + 8 * i) := vu.trans val_old
  refine WP.mono (wordSelectStore_ok cu.scr ((ku.gpr (by decide)).trans po)
    ((ku.gpr (by decide)).trans pt) hi cu.hZ) fun v ⟨⟨mv, pv, qv, cv⟩, kv⟩ => ?_
  rw [mu, val] at mv
  have ov : Outside B (slot w 5 + 8 * i) 8 t.mem v.mem := by
    rw [mv]; exact writeW_outside _ _ _ (by omega_arith)
  have ov_full : Outside B (slot w 5) (8 * w) t.mem v.mem := ov.mono (by omega_arith) (by omega_arith)
  have cv' := cu.of kv (by decide) (by rw [mu]; exact arrO ov_full (by decide) (by decide))
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
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
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
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold window
  refine WP.seq (WP.mono (sq_ok h hodd ha (X := X) (c := c)) fun s₁ ⟨⟨c1, o1, f1, l1, e1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c1 hodd l1 (X := X) (c := c + c)) fun s₂ ⟨⟨c2, o2, f2, l2, e2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c2 hodd l2 (X := X) (c := c + c + (c + c)))
    fun s₃ ⟨⟨c3, o3, f3, l3, e3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (sq_ok c3 hodd l3 (X := X) (c := c + c + (c + c) + (c + c + (c + c))))
    fun s₄ ⟨⟨c4, o4, f4, l4, e4⟩, k4⟩ => ?_)
  have k14 := ((k1.trans k2).trans k3).trans k4
  have f14 := (f1.trans f2).trans (f3.trans f4)
  have hd := (s.gpr .s7).isLt
  have hd16 : (s.gpr .s7).toNat / 2 ^ 60 < 16 := by omega_arith
  refine WP.seq (WP.mono (WP.keep [.a1] (Q := fun t =>
      t.gpr .a1 = BitVec.ofNat 64 ((s.gpr .s7).toNat / 2 ^ 60) ∧ t.mem = s₄.mem)
    (by brun [top_nibble, k14.gpr (r := .s7) (by decide)]) (by rfl) (by rfl)) fun s₅ ⟨⟨a1, m5⟩, k5⟩ => ?_)
  have c5 := c4.regs k5 (by decide) m5
  refine WP.seq (WP.mono (select_ok c5 a1 hd16) fun s₆ ⟨⟨a6, v6, c6, o6⟩, k6⟩ => ?_)
  have A6 : A s₆.mem B w 6 = A s₄.mem B w 6 := by rw [v6 6 (by decide) (by decide) (by decide), m5]
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
  have hb256 : b < 256 := by rw [← hb]; exact (u.mem (off D i)).isLt
  have tab : ∀ {m : Mem}, Fix B w t₀.mem m → ∀ i < 16, A m B w (8 + i) < N ∧
      (RR = 2 ^ (64 * w) * 2 ^ (64 * w) % N → A m B w (8 + i) % N = X ^ i * 2 ^ (64 * w) % N) :=
    fun hf i hi => by
      rw [hf (8 + i) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
      exact htab i hi
  unfold byteWin
  refine WP.seq (WP.mono (lbu_ok h9 hrd) fun u₁ ⟨⟨a7, a9, m1⟩, k1⟩ => ?_)
  rw [hb] at a7
  have c1 := h.ctx.regs k1 (by decide) m1
  have f1 : Fix B w t₀.mem u₁.mem := by rw [m1]; exact h.fix
  refine WP.seq (WP.mono (window_ok c1 hodd (by rw [m1]; exact h.lt) (fun i hi => (tab f1 i hi).1)
    (X := X) (c := c)) fun u₂ ⟨⟨c2, o2, f2, l2, a7', e2⟩, k2⟩ => ?_)
  refine WP.mono (window_ok c2 hodd l2 (fun i hi => (tab (f1.trans f2) i hi).1) (X := X) (c := 16 * c + b / 16))
    fun t ⟨⟨c3, o3, f3, l3, _, e3⟩, k3⟩ => ⟨⟨c3, ?_, f1.trans (f2.trans f3), l3, fun hE => ?_, ?_⟩, ?_, ?_⟩
  · rw [m1] at o2; exact (h.out.trans o2).trans o3
  · have p1 := e2 (by rw [m1]; exact h.pw hE) (fun i hi => (tab f1 i hi).2 hE)
    rw [a7, nib_hi hb256] at p1
    have p2 := e3 p1 (fun i hi => (tab (f1.trans f2) i hi).2 hE)
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
  have h0 : WCtx s B Z w (A s.mem B w 0) := ⟨hs, hw2, hw', hZ, h7, h5, ht0, hinv, rfl⟩
  have hn := h0.nw
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd hRRlt ⊢
  replace h0 : WCtx s B Z w N := hNd ▸ h0
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  generalize hXd : wordsVal s.mem B (slot w 4) w = X
  generalize hRRd : wordsVal s.mem B (slot w 1) w = RR at hRRlt ⊢
  unfold powWin
  refine WP.seq (WP.mono (table_ok h0 hN hodd (by rw [show A s.mem B w 1 = RR from hRRd]; exact hRRlt))
    fun t₀ ⟨⟨c0, o0, t01, _, t7, a6, htab⟩, k0⟩ => ?_)
  rw [show A s.mem B w 4 = X from hXd, show A s.mem B w 1 = RR from hRRd] at htab
  have r0 : Run s t₀ t₀ B Z w N X RR 0 := ⟨c0, o0, fun _ _ _ _ _ _ => rfl, by rw [a6]; exact (htab 0 (by decide)).1,
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
      have e24 := slot24 w
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
  have t7' : A u.mem B w 7 = 1 := by rw [hu.fix 7 (by decide) (by decide) (by decide) (by decide) (by decide), t7]
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

end VG.Proof.Bignum.RISCV64.Win
