module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Twos
public import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the square root

A step of the square root (`sqrtStep_ok`) is `RecoverDet.sqrtStep` on the
radicand (wide array 7, narrow 14 and 15), the remainder (array 4) and the
root (array 5): two doublings of each of the radicand and the remainder,
the carry of each of the radicand's into the remainder; `4 y + 1` (array 6),
the difference (array 7) and its borrow (`sC`), the remainder selected, and
the root doubled with the borrow's complement.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet (sqrtStep)

/-- `2 a + b` modulo `2^N`, for a bit `b`. -/
theorem mod_add_bit {a b N : Nat} (hb : b ≤ 1) (hN : 1 ≤ N) : (2 * a + b) % 2 ^ N = 2 * a % 2 ^ N + b := by
  have hM : 2 ^ N = 2 * 2 ^ (N - 1) := by rw [← Nat.pow_succ']; congr 1; omega_arith
  rw [hM, Nat.mul_mod_mul_left]
  have hK := Nat.mod_lt a (Nat.two_pow_pos (N - 1))
  rw [Nat.add_mod, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt (show b < 2 * 2 ^ (N - 1) by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

/-- A doubling with a carry in and out. -/
theorem dbl_val {X X' c₀ P : Nat} {c : Bool} (h : X' + P * c.toNat = 2 * X + c₀) (hX' : X' < P) :
    X' = (2 * X + c₀) % P ∧ c.toNat = (2 * X + c₀) / P := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX', Nat.add_mul_div_left _ _ (by omega_arith),
    Nat.div_eq_of_lt hX']
  exact ⟨rfl, by omega_arith⟩

/-- The carry in of a doubling, from a mask in a header slot. -/
theorem shlPre_mask {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {pre : List Instr} {c : Bool}
    (hm : MaskPre B Z s.mem pre c) :
    ∀ t : State, t.mem = s.mem → t.gpr .rbp = s.gpr .rbp → t.gpr .rdi = s.gpr .rdi → t.rd = s.rd → t.wr = s.wr →
      WP isa (.block pre) t fun t' => (t'.gpr .rbp = mask c ∧ t'.mem = t.mem) ∧ Keep [.rbp] t t' :=
  fun t hm' _ hdi _ hw => hm t (h.scr.congr hw) (hdi.trans h.rdi) fun i _ => by rw [hm']

/-- The carry in of a doubling, already in `rbp`. -/
theorem shlPre_nil {s : State} {c : Bool} (hc : s.gpr .rbp = mask c) :
    ∀ t : State, t.mem = s.mem → t.gpr .rbp = s.gpr .rbp → t.gpr .rdi = s.gpr .rdi → t.rd = s.rd → t.wr = s.wr →
      WP isa (.block []) t fun t' => (t'.gpr .rbp = mask c ∧ t'.mem = t.mem) ∧ Keep [.rbp] t t' :=
  fun _ _ hbp _ _ _ => WP.block_nil ⟨⟨hbp.trans hc, rfl⟩, Keep.refl _ _⟩

/-- `[store sC rbp]`. -/
theorem storeC_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block [.store (hdr sC) .rbp]) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sC)) (s.gpr .rbp) ∧ Keep [] s t := by
  have h256 := h.h256
  refine WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sC)) (s.gpr .rbp)) ?_ rfl
  xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.st (d := 8 * sC) (by simp only [sC, sFn]; omega_arith)]

/-- The step of the code is `sqrtStep`. -/
theorem sqrtStep_code {nb wb XS R Y XS1 XS2 R1 R2 T1 T2 D R3 Y1 : Nat} {c1 c2 c3 c4 c6 c7 c11 : Bool}
    (hnb : 1 ≤ nb)
    (e1 : XS1 + 2 ^ wb * c1.toNat = 2 * XS + false.toNat) (l1 : XS1 < 2 ^ wb)
    (e2 : R1 + 2 ^ nb * c2.toNat = 2 * R + c1.toNat) (l2 : R1 < 2 ^ nb)
    (e3 : XS2 + 2 ^ wb * c3.toNat = 2 * XS1 + false.toNat) (l3 : XS2 < 2 ^ wb)
    (e4 : R2 + 2 ^ nb * c4.toNat = 2 * R1 + c3.toNat) (l4 : R2 < 2 ^ nb)
    (e6 : T1 + 2 ^ nb * c6.toNat = 2 * Y + false.toNat) (l6 : T1 < 2 ^ nb)
    (e7 : T2 + 2 ^ nb * c7.toNat = 2 * T1 + true.toNat) (l7 : T2 < 2 ^ nb)
    (e8 : D + T2 = R2 + 2 ^ nb * (decide (R2 < T2)).toNat)
    (e10 : R3 = if decide (R2 < T2) then R2 else D)
    (e11 : Y1 + 2 ^ nb * c11.toNat = 2 * Y + (!decide (R2 < T2)).toNat) (l11 : Y1 < 2 ^ nb) :
    (XS2, R3, Y1) = sqrtStep nb wb (XS, R, Y) := by
  have b1 := Bool.toNat_le c1
  have b3 := Bool.toNat_le c3
  obtain ⟨v1, d1⟩ := dbl_val e1 l1
  obtain ⟨v2, _⟩ := dbl_val e2 l2
  obtain ⟨v3, d3⟩ := dbl_val e3 l3
  obtain ⟨v4, _⟩ := dbl_val e4 l4
  obtain ⟨v6, _⟩ := dbl_val e6 l6
  obtain ⟨v7, _⟩ := dbl_val e7 l7
  obtain ⟨v11, _⟩ := dbl_val e11 l11
  simp only [Bool.toNat_false, Nat.add_zero, Bool.toNat_true] at v1 d1 v3 d3 v6 v7
  rw [mod_add_bit b1 hnb] at v2
  rw [mod_add_bit b3 hnb] at v4
  rw [mod_add_bit (by decide) hnb] at v7
  rw [mod_add_bit (Bool.toNat_le _) hnb] at v11
  unfold sqrtStep
  simp only
  rw [← v1, ← d1, ← v2, ← v3, ← d3, ← v4, ← v6, ← v7]
  by_cases hc : R2 < T2
  · simp only [hc, decide_true, ↓reduceIte, Bool.not_true, Bool.toNat_false, Nat.add_zero] at e10 v11 ⊢
    rw [e10, v11, v6]
  · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.toNat_true,
      Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e8 e10 v11 ⊢
    rw [e10, v11, v6, show D = R2 - T2 by omega_arith]

end VG.Proof.Rsa.X86_64.Rd

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet (sqrtStep)

/-- What the square root changes: arrays 4 to 7, wide array 7, and the
header slots 25 and 30. -/
def SqrtP (w y : Nat) : Prop :=
  (slot w 4 ≤ y ∧ y < slot w 8) ∨ (slot w 14 ≤ y ∧ y < slot w 14 + 8 * (2 * w + 2)) ∨ (200 ≤ y ∧ y < 208) ∨
    (240 ≤ y ∧ y < 248)

abbrev sqrtClob : List Reg := [.r12, .r9, .rbx, .rbp, .rax, .r14, .rsi, .r8, .r10, .rdx]

/-- After `j` steps of the square root from `s₀`, with `st` the radicand,
the remainder and the root there. -/
structure SqrtInv (s₀ : State) (B : Addr) (Z w : Nat) (st : Nat × Nat × Nat) (j : Nat) (t : State) : Prop where
  ws : Ws t B Z w
  frm : FrmP B (SqrtP w) s₀.mem t.mem
  keep : Keep sqrtClob s₀ t
  ct : word t.mem B (8 * sCt) = BitVec.ofNat 64 (64 * (w + 1) - j)
  val : (wv t.mem B (slot w 14) (2 * w + 2), wv t.mem B (slot w 4) w, wv t.mem B (slot w 5) w) =
    (sqrtStep (64 * w) (64 * (2 * w + 2)))^[j] st

macro "sq_omega" : tactic =>
  `(tactic| (simp only [SqrtP, DOk, Bignum.slot, hdrBytes, sC, sCt, sFn, shlN, ↓reduceIte, Bool.false_eq_true]; omega_arith))

/-- A step of the square root is `sqrtStep`. -/
theorem sqrtStep_ok {s₀ t : State} {B : Addr} {Z w : Nat} {st : Nat × Nat × Nat} {j : Nat}
    (hI : SqrtInv s₀ B Z w st j t) (hj : j < 64 * (w + 1)) :
    WP isa sqrtBody t fun t' => t'.zf = some (decide (j + 1 = 64 * (w + 1))) ∧ SqrtInv s₀ B Z w st (j + 1) t' := by
  have h := hI.ws
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  have hw2 := h.w2
  generalize hXS : wv t.mem B (slot w 14) (2 * w + 2) = XS
  generalize hR : wv t.mem B (slot w 4) w = R
  generalize hY : wv t.mem B (slot w 5) w = Y
  have hval := hI.val
  rw [hXS, hR, hY] at hval
  unfold sqrtBody
  simp only [seqs]
  -- The radicand doubled: its top bit `hi` out.
  refine WP.seq (WP.mono (shlA_ok h true (j := 14) (c₀ := false) (by decide) (shlPre_mask h maskZero))
    fun t₁ ⟨c1, hc1, e1, o1, k1⟩ => ?_)
  simp only [shlN, ↓reduceIte] at e1 o1
  rw [hXS] at e1
  have h₁ := h.congrO o1 (by sq_omega) k1 (by simp)
  have R₁ : wv t₁.mem B (slot w 4) w = R := by rw [o1.wv (by sq_omega) (by sq_omega), hR]
  have Y₁ : wv t₁.mem B (slot w 5) w = Y := by rw [o1.wv (by sq_omega) (by sq_omega), hY]
  -- The remainder doubled with `hi`.
  refine WP.seq (WP.mono (shlA_ok h₁ false (j := 4) (c₀ := c1) (by decide) (shlPre_nil hc1))
    fun t₂ ⟨c2, hc2, e2, o2, k2⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at e2 o2
  rw [R₁] at e2
  have h₂ := h₁.congrO o2 (by sq_omega) k2 (by simp)
  have X₂ : wv t₂.mem B (slot w 14) (2 * w + 2) = wv t₁.mem B (slot w 14) (2 * w + 2) :=
    o2.wv (by sq_omega) (by sq_omega)
  have Y₂ : wv t₂.mem B (slot w 5) w = Y := by rw [o2.wv (by sq_omega) (by sq_omega), Y₁]
  -- The radicand doubled again: `lo` out.
  refine WP.seq (WP.mono (shlA_ok h₂ true (j := 14) (c₀ := false) (by decide) (shlPre_mask h₂ maskZero))
    fun t₃ ⟨c3, hc3, e3, o3, k3⟩ => ?_)
  simp only [shlN, ↓reduceIte] at e3 o3
  rw [X₂] at e3
  have h₃ := h₂.congrO o3 (by sq_omega) k3 (by simp)
  have R₃ : wv t₃.mem B (slot w 4) w = wv t₂.mem B (slot w 4) w := o3.wv (by sq_omega) (by sq_omega)
  have Y₃ : wv t₃.mem B (slot w 5) w = Y := by rw [o3.wv (by sq_omega) (by sq_omega), Y₂]
  -- The remainder doubled with `lo`.
  refine WP.seq (WP.mono (shlA_ok h₃ false (j := 4) (c₀ := c3) (by decide) (shlPre_nil hc3))
    fun t₄ ⟨c4, _, e4, o4, k4⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at e4 o4
  rw [R₃] at e4
  have h₄ := h₃.congrO o4 (by sq_omega) k4 (by simp)
  have X₄ : wv t₄.mem B (slot w 14) (2 * w + 2) = wv t₃.mem B (slot w 14) (2 * w + 2) :=
    o4.wv (by sq_omega) (by sq_omega)
  have Y₄ : wv t₄.mem B (slot w 5) w = Y := by rw [o4.wv (by sq_omega) (by sq_omega), Y₃]
  -- `t := 4 y + 1`.
  refine WP.seq (WP.mono (copyA_ok h₄ (o := 6) (a := 5) (by decide) (by decide) (by decide))
    fun t₅ ⟨v5, o5, k5⟩ => ?_)
  rw [Y₄] at v5
  have h₅ := h₄.congrO o5 (by sq_omega) k5 (by simp)
  refine WP.seq (WP.mono (shlA_ok h₅ false (j := 6) (c₀ := false) (by decide) (shlPre_mask h₅ maskZero))
    fun t₆ ⟨c6, _, e6, o6, k6⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at e6 o6
  rw [v5] at e6
  have h₆ := h₅.congrO o6 (by sq_omega) k6 (by simp)
  refine WP.seq (WP.mono (shlA_ok h₆ false (j := 6) (c₀ := true) (by decide) (shlPre_mask h₆ maskOnes))
    fun t₇ ⟨c7, _, e7, o7, k7⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at e7 o7
  have h₇ := h₆.congrO o7 (by sq_omega) k7 (by simp)
  have R₇ : wv t₇.mem B (slot w 4) w = wv t₄.mem B (slot w 4) w := by
    rw [o7.wv (by sq_omega) (by sq_omega), o6.wv (by sq_omega) (by sq_omega), o5.wv (by sq_omega) (by sq_omega)]
  -- The difference and its borrow.
  refine WP.seq (WP.mono (subA_ok h₇ (t := 7) (a := 4) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₈ ⟨hc8, e8, o8, k8⟩ => ?_)
  rw [R₇] at hc8 e8
  have h₈ := h₇.congrO o8 (by sq_omega) k8 (by simp)
  refine WP.seq (WP.mono (storeC_ok h₈) fun t₉ ⟨m9, k9⟩ => ?_)
  rw [hc8] at m9
  have h₉ := h₈.congrW m9 (by unfold DOk; simp only [sC, sFn]; omega_arith) (by decide) k9 (by simp)
  have hsC : word t₉.mem B (8 * sC) = mask (decide (wv t₄.mem B (slot w 4) w < wv t₇.mem B (slot w 6) w)) := by
    rw [m9, word_writeW_self]
  have o9 : Outside B (8 * sC) 8 t₈.mem t₉.mem := by
    rw [m9]; exact writeW_outside _ _ _ (by sq_omega)
  -- The remainder selected.
  refine WP.seq (WP.mono (selPre_ok h₉ false (j := 4) (o := 7) (by decide) (by decide) (by sq_omega)
    (maskLd (by decide) h256 hsC)) fun t₁₀ ⟨v10, o10, k10⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at v10 o10
  have h₁₀ := h₉.congrO o10 (by sq_omega) k10 (by simp)
  have hsC₁₀ : word t₁₀.mem B (8 * sC) = mask (decide (wv t₄.mem B (slot w 4) w < wv t₇.mem B (slot w 6) w)) := by
    rw [o10.word (by sq_omega) (by sq_omega), hsC]
  -- The root doubled with the complement of the borrow.
  refine WP.seq (WP.mono (shlA_ok h₁₀ false (j := 5) (by decide) (shlPre_mask h₁₀ (maskNot (by decide) h256 hsC₁₀)))
    fun t₁₁ ⟨c11, _, e11, o11, k11⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at e11 o11
  have h₁₁ := h₁₀.congrO o11 (by sq_omega) k11 (by simp)
  -- The count.
  have hct : word t₁₁.mem B (8 * sCt) = BitVec.ofNat 64 (64 * (w + 1) - j) := by
    rw [o11.word (by sq_omega) (by sq_omega), o10.word (by sq_omega) (by sq_omega), o9.word (by sq_omega) (by sq_omega),
      o8.word (by sq_omega) (by sq_omega), o7.word (by sq_omega) (by sq_omega), o6.word (by sq_omega) (by sq_omega),
      o5.word (by sq_omega) (by sq_omega), o4.word (by sq_omega) (by sq_omega), o3.word (by sq_omega) (by sq_omega),
      o2.word (by sq_omega) (by sq_omega), o1.word (by sq_omega) (by sq_omega)]
    exact hI.ct
  refine WP.mono (countNext_ok h₁₁ hct (by omega_arith) (by omega_arith)) fun t₁₂ ⟨hz, m12, k12⟩ => ⟨?_, ?_⟩
  · rw [hz]; congr 1; simp only [decide_eq_decide]; omega_arith
  have o12 : Outside B (8 * sCt) 8 t₁₁.mem t₁₂.mem := by rw [m12]; exact writeW_outside _ _ _ (by sq_omega)
  have kk := (((((((((((hI.keep.trans k1).trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans
    k8).trans k9).trans k10).trans k11).trans k12
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → SqrtP w y) →
      FrmP B (SqrtP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨h₁₁.congrW m12 (by unfold DOk; simp only [sCt, sFn]; omega_arith) (by decide) k12 (by simp),
    (((((((((((hI.frm.trans (fr o1 fun y => by sq_omega)).trans (fr o2 fun y => by sq_omega)).trans
      (fr o3 fun y => by sq_omega)).trans (fr o4 fun y => by sq_omega)).trans (fr o5 fun y => by sq_omega)).trans
      (fr o6 fun y => by sq_omega)).trans (fr o7 fun y => by sq_omega)).trans (fr o8 fun y => by sq_omega)).trans
      (fr o9 fun y => by sq_omega)).trans (fr o10 fun y => by sq_omega)).trans (fr o11 fun y => by sq_omega)).trans
      (fr o12 fun y => by sq_omega),
    kk.mono (by simp), by rw [m12, word_writeW_self, Nat.sub_sub], ?_⟩
  -- The values.
  have Y₁₀ : wv t₁₀.mem B (slot w 5) w = Y := by
    rw [o10.wv (by sq_omega) (by sq_omega), o9.wv (by sq_omega) (by sq_omega), o8.wv (by sq_omega) (by sq_omega),
      o7.wv (by sq_omega) (by sq_omega), o6.wv (by sq_omega) (by sq_omega), o5.wv (by sq_omega) (by sq_omega), Y₄]
  rw [Y₁₀] at e11
  have T₈ : wv t₈.mem B (slot w 6) w = wv t₇.mem B (slot w 6) w := o8.wv (by sq_omega) (by sq_omega)
  have R₈ : wv t₈.mem B (slot w 4) w = wv t₄.mem B (slot w 4) w := by rw [o8.wv (by sq_omega) (by sq_omega), R₇]
  rw [o9.wv (by sq_omega) (by sq_omega), o9.wv (by sq_omega) (by sq_omega), R₈] at v10
  have step := sqrtStep_code (nb := 64 * w) (wb := 64 * (2 * w + 2)) (by omega_arith) e1 (wv_lt _ _ _ _) e2
    (wv_lt _ _ _ _) e3 (wv_lt _ _ _ _) e4 (wv_lt _ _ _ _) e6 (wv_lt _ _ _ _) e7 (wv_lt _ _ _ _) e8 v10 e11
    (wv_lt _ _ _ _)
  rw [Function.iterate_succ_apply', ← hval, ← step,
    o12.wv (by sq_omega) (by sq_omega), o12.wv (by sq_omega) (by sq_omega), o12.wv (by sq_omega) (by sq_omega),
    o11.wv (by sq_omega) (by sq_omega), o11.wv (by sq_omega) (by sq_omega),
    o10.wv (by sq_omega) (by sq_omega), o9.wv (by sq_omega) (by sq_omega), o8.wv (by sq_omega) (by sq_omega),
    o7.wv (by sq_omega) (by sq_omega), o6.wv (by sq_omega) (by sq_omega), o5.wv (by sq_omega) (by sq_omega), X₄]

end VG.Proof.Rsa.X86_64.Rd

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet (sqrtStep)

/-- The square root's loop: `64 (w + 1)` steps of `sqrtStep`, with the count in
the header. -/
theorem sqrtLoop_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hct : word s.mem B (8 * sCt) = BitVec.ofNat 64 (64 * (w + 1))) :
    WP isa (.loop sqrtBody .ne) s fun t => SqrtInv s B Z w
      (wv s.mem B (slot w 14) (2 * w + 2), wv s.mem B (slot w 4) w, wv s.mem B (slot w 5) w) (64 * (w + 1)) t :=
  wp_upto (a := 0) (N := 64 * (w + 1)) (by omega_arith) _ (fun j _ hj t hI => sqrtStep_ok hI hj)
    (fun _ h => h) ⟨h, FrmP.refl _ _ _, Keep.refl _ _, by rw [Nat.sub_zero]; exact hct, rfl⟩

end VG.Proof.Rsa.X86_64.Rd
