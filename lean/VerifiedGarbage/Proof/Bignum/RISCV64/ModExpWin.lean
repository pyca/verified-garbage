module

-- separate module: the windowed exponentiation, the largest of the CRT's proofs, which only `CrtPower` uses
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontSqr
public import VerifiedGarbage.Impl.Bignum.RISCV64.ModExp
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontRounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
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

end VG.Proof.Bignum.RISCV64.Win
