module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# The comb's digits, on PPC64LE

As on 32-bit ARM (`Proof/Weierstrass/Arm/TCombDigit.lean`, `TCombSign.lean`):
the window `k_j` read from the table of the scalar's bits by Horner's rule
(only the last window's real bits), the magnitude `|k_j - H|` of its digit,
and the mask of its sign.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.TComb

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE

/-- `r9 = Σ_{i<k} 2^i v (d + i)` from the bytes `v (d + i)` at `bits + d + i`
from `r4`. -/
theorem hornerAt_ok (K : TCombCfg) {v : Nat → Nat} (hv : ∀ i, v i ≤ 1) {base : Addr} {W : Nat} :
    ∀ k d (s : State), Ws s base 8192 → At s base .r4 W → k < 63 → K.L.bits + d + k < 2 ^ 15 →
    W + K.L.bits + d + k ≤ 8192 →
    (∀ i < k, s.mem (off base (W + K.L.bits + d + i)) = BitVec.ofNat 8 (v (d + i))) →
    WP isa (.block (K.hornerAt d k)) s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (hornerVal v d k) ∧ Kp [.r5, .r9] s t ∧ t.mem = s.mem
  | 0, d, s, _, _, _, _, _, _ => by
    unfold TCombCfg.hornerAt
    refine wp_step (exec_li (by decide)) (WP.block_nil ⟨?_, Kp.write _ _ (by decide), rfl⟩)
    simp only [write_gpr, ite_true]; rfl
  | k + 1, d, s, hs, h4, hk, ho, hw, hb => by
    rw [TCombCfg.hornerAt]
    refine wp_append (WP.mono (hornerAt_ok K hv k (d + 1) s hs h4 (by omega) (by omega) (by omega)
      fun i hi => by
        rw [show W + K.L.bits + (d + 1) + i = W + K.L.bits + d + (i + 1) by omega,
          show d + 1 + i = d + (i + 1) by omega]
        exact hb (i + 1) (by omega)) fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
    have h0 := hb 0 (by omega)
    simp only [Nat.add_zero] at h0
    refine wp_step exec_add ?_
    refine wp_step (lbz_ok ((k₁.ws hs).write _ _) ((k₁.at h4).write (d := .r9) _) (by decide)
      (d := K.L.bits + d) (by omega)) ?_
    refine wp_step exec_add (WP.block_nil ?_)
    simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
    refine ⟨?_, k₁.trans ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide)))), m₁⟩
    rw [v₁, m₁, show W + (K.L.bits + d) = W + K.L.bits + d by omega, h0]
    have hn := hornerVal_lt hv (d + 1) k
    have hvd := hv d
    have hp : 2 ^ k < 2 ^ 62 := Nat.pow_lt_pow_right (by decide) (by omega)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, hornerVal]
    rw [Nat.mod_eq_of_lt (by omega : hornerVal v (d + 1) k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : v d < 2 ^ 8), Nat.mod_eq_of_lt (by omega : v d < 2 ^ 64)]
    omega

/-- `r4 = r3 + w j`, for `j` in `r31`. -/
theorem windowIndex_ok (K : TCombCfg) {s : State} {base : Addr} {j : Nat}
    (h3 : At s base .r3 0) (hw : K.w < 2 ^ 15) (gj : s.gpr .r31 = BitVec.ofNat 64 j) :
    WP isa (.block K.windowIndex) s fun t =>
      At t base .r4 (K.w * j) ∧ Kp [.r4] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.windowIndex
  refine wp_step (exec_li hw) ?_
  refine wp_step exec_mul ?_
  refine wp_step exec_add (WP.block_nil ?_)
  refine ⟨?_, ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide)), rfl⟩
  simp only [At, write_gpr, ite_true, reduceCtorEq, ite_false]
  rw [h3, gj, ← BitVec.ofNat_mul, off, off, BitVec.add_zero]

/-- `r6 = r31 - (J - 1)`, zero exactly for the last window. -/
theorem lastTest_ok (K : TCombCfg) {s : State} {j : Nat} (hj : j < 2 ^ 64) (hJ : K.J - 1 ≤ 2 ^ 15)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j) :
    WP isa (.block K.lastTest) s fun t =>
      isa.eval TCombCfg.isLast t = some (decide (j = K.J - 1)) ∧ Kp [.r6] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.lastTest
  refine wp_step (exec_subi (by decide) hJ) (WP.block_nil ⟨?_, Kp.write _ _ (by decide), rfl⟩)
  rw [eval_zero]
  simp only [write_gpr, ite_true, gj]
  congr 1
  by_cases e : j = K.J - 1
  · rw [e, BitVec.sub_self]; simp
  · have hne : BitVec.ofNat 64 j - BitVec.ofNat 64 (K.J - 1) ≠ 0#64 := fun h0 => by
      have e' := congrArg (fun z : BitVec 64 => z + BitVec.ofNat 64 (K.J - 1)) h0
      simp only [BitVec.sub_add_cancel, BitVec.zero_add] at e'
      have := congrArg BitVec.toNat e'
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by omega)] at this
      exact e this
    simp [hne, e]

/-- The 64-bit signed-digit magnitude. -/
theorem magH_fact64 : ∀ w < 9, ∀ v < 2 ^ w,
    (BitVec.ofNat 64 v - BitVec.ofNat 64 (2 ^ (w - 1)) ^^^
        (BitVec.ofNat 64 0 - (BitVec.ofNat 64 v - BitVec.ofNat 64 (2 ^ (w - 1))) >>> 63)) -
      (BitVec.ofNat 64 0 - (BitVec.ofNat 64 v - BitVec.ofNat 64 (2 ^ (w - 1))) >>> 63) =
      BitVec.ofNat 64 (magH (2 ^ (w - 1)) v) := by
  decide +kernel

/-- `r9 = |v - H|` from the window `v` in `r9`. -/
theorem magnitude_ok (K : TCombCfg) {s : State} {v : Nat} (hw : K.w < 9) (hv : v < 2 ^ K.w)
    (gv : s.gpr .r9 = BitVec.ofNat 64 v) :
    WP isa (.block K.magnitude) s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (magH K.H v) ∧ Kp [.r4, .r5, .r9] s t ∧ t.mem = s.mem := by
  have hH : K.H ≤ 2 ^ 15 := Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 15 by omega))
    (by decide)
  unfold TCombCfg.magnitude
  refine wp_step (exec_subi (by decide) hH) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_sub (WP.block_nil ?_)
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, gv]
    exact magH_fact64 K.w hw v hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The window's `count` bits by Horner's rule. -/
theorem hornerWindow_ok (K : TCombCfg) {s : State} {base : Addr} {j count : Nat}
    (hs : Ws s base 8192) (h4 : At s base .r4 (K.w * j)) (hc : count ≤ K.w) (hw : K.w < 9)
    (ho : K.L.bits + K.w < 2 ^ 15) (hl : K.w * j + K.L.bits + count ≤ 8192)
    {v : Nat → Nat} (hv : ∀ i, v i ≤ 1)
    (hb : ∀ i < count, s.mem (off base (K.L.bits + K.w * j + i)) = BitVec.ofNat 8 (v i)) :
    WP isa (.block (K.horner count)) s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (hornerVal v 0 count) ∧ Kp [.r5, .r9] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.horner
  exact hornerAt_ok K hv count 0 s hs h4 (by omega) (by omega) (by omega) fun i hi => by
    rw [show K.w * j + K.L.bits + 0 + i = K.L.bits + K.w * j + i by omega, Nat.zero_add]
    exact hb i hi

/-- The digit's magnitude `|k_j - H|` into `r9`, from the window's bits
(only its real ones, for the last window). -/
theorem digit_ok (K : TCombCfg) {s : State} {base : Addr} {j k : Nat}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hw : K.w < 9) (hj : j < K.J) (hJ : K.J ≤ 2 ^ 15)
    (start : K.w * (K.J - 1) ≤ K.L.nbits) (cover : K.L.nbits ≤ K.w * K.J)
    (ho : K.L.bits + K.w < 2 ^ 15) (hl : K.L.bits + K.L.nbits ≤ 8192) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hb : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0) :
    WP isa K.digit s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (magH K.H (combWin K.w k j)) ∧ Kp [.r4, .r5, .r6, .r9] s t ∧
        t.mem = s.mem := by
  let count := if j = K.J - 1 then K.topBits else K.w
  have bounds := windowBits_bounds hj start cover
  change count ≤ K.w ∧ K.w * j + count ≤ K.L.nbits ∧ (count = K.w ∨ K.w * j + count = K.L.nbits) at bounds
  let v := fun i => (k.testBit (K.w * j + i)).toNat
  have hv : ∀ i, v i ≤ 1 := fun i => by dsimp only [v]; cases k.testBit (K.w * j + i) <;> decide
  have bytes : ∀ i < count, s.mem (off base (K.L.bits + K.w * j + i)) = BitVec.ofNat 8 (v i) := by
    intro i hi
    rw [show K.L.bits + K.w * j + i = K.L.bits + (K.w * j + i) by omega, hb _ (by omega)]
    dsimp only [v]
    cases k.testBit (K.w * j + i) <;> rfl
  unfold TCombCfg.digit
  rw [WP.seq_iff]
  refine WP.mono (windowIndex_ok K h3 (by omega) gj) fun s₁ ⟨p₁, k₁, m₁⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (lastTest_ok K (j := j) (by omega) (by omega) (by rw [k₁.g]; exact gj))
    fun s₂ ⟨z₂, k₂, m₂⟩ => ?_
  have k₁₂ : Kp [.r4, .r6] s s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have hh := hornerWindow_ok K (s := s₂) (j := j) (count := count) (k₁₂.ws hs)
    (by rw [At, k₂.g]; exact p₁) bounds.1 hw ho (by omega) hv
    (by intro i hi; rw [m₂, m₁]; exact bytes i hi)
  have decode : WP isa (.ite TCombCfg.isLast (.block (K.horner K.topBits)) (.block (K.horner K.w))) s₂
      fun t => t.gpr .r9 = BitVec.ofNat 64 (hornerVal v 0 count) ∧ Kp [.r5, .r9] s₂ t ∧ t.mem = s₂.mem := by
    by_cases h : j = K.J - 1
    · refine WP.ite true (by rw [z₂]; simp [h]) (fun _ => ?_) (fun hf => by cases hf)
      simpa only [count, h, ↓reduceIte] using hh
    · refine WP.ite false (by rw [z₂]; simp [h]) (fun ht => by cases ht) (fun _ => ?_)
      simpa only [count, h, ↓reduceIte] using hh
  rw [WP.seq_iff]
  refine WP.mono decode fun s₃ ⟨v₃, k₃, m₃⟩ => ?_
  have hvlt : hornerVal v 0 count < 2 ^ K.w :=
    Nat.lt_of_lt_of_le (hornerVal_lt hv 0 count) (Nat.pow_le_pow_right (by decide) bounds.1)
  refine WP.mono (magnitude_ok K hw hvlt v₃) fun s₄ ⟨v₄, k₄, m₄⟩ => ⟨?_, ?_, by rw [m₄, m₃, m₂, m₁]⟩
  · rw [v₄]
    change BitVec.ofNat 64 (magH K.H (hornerVal v 0 count)) = _
    rw [window_without_padding bounds.1 bounds.2.2 hk]
  · exact ((k₁₂.mono (by decide)).trans (k₃.mono (by decide))).trans (k₄.mono (by decide))

/-- The mask `r10` of the window's top bit being clear. -/
theorem signRead_ok (K : TCombCfg) {s : State} {base : Addr} {j : Nat} {b : Bool}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hw : 1 ≤ K.w ∧ K.w < 9)
    (ho : K.L.bits + K.w < 2 ^ 15) (hl : K.L.bits + K.w * j + K.w ≤ 8192)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hb : s.mem (off base (K.L.bits + K.w * j + K.w - 1)) = if b then 1 else 0) :
    WP isa (.block K.signRead) s fun t =>
      t.gpr .r10 = (if b then 0 else BitVec.allOnes 64) ∧ Kp [.r4, .r10] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.signRead
  refine wp_append (WP.mono (windowIndex_ok K h3 (by omega) gj) fun s₁ ⟨p₁, k₁, m₁⟩ => ?_)
  refine wp_step (lbz_ok (k₁.ws hs) p₁ (by decide) (d := K.L.bits + K.w - 1) (by omega)) ?_
  refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false]
  refine ⟨?_, (k₁.mono (by decide)).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))), m₁⟩
  rw [m₁, show K.w * j + (K.L.bits + K.w - 1) = K.L.bits + K.w * j + K.w - 1 by omega, hb]
  cases b <;> rfl

/-- The mask `r10` of the digit `k_j - H` being negative. -/
theorem signMask_ok (K : TCombCfg) {s : State} {base : Addr} {j k : Nat}
    (hs : Ws s base 8192) (h3 : At s base .r3 0) (hw : 1 ≤ K.w ∧ K.w < 9) (hj : j < K.J)
    (hJ : K.J ≤ 2 ^ 15) (start : K.w * (K.J - 1) ≤ K.L.nbits) (cover : K.L.nbits ≤ K.w * K.J)
    (ho : K.L.bits + K.w < 2 ^ 15) (hl : K.L.bits + K.L.nbits ≤ 8192) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hb : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0) :
    WP isa K.signMask s fun t =>
      t.gpr .r10 = (if K.H ≤ combWin K.w k j then 0 else BitVec.allOnes 64) ∧
        Kp [.r4, .r6, .r10] s t ∧ t.mem = s.mem := by
  have bounds := windowBits_bounds hj start cover
  change (if j = K.J - 1 then K.topBits else K.w) ≤ K.w ∧
    K.w * j + (if j = K.J - 1 then K.topBits else K.w) ≤ K.L.nbits ∧
    ((if j = K.J - 1 then K.topBits else K.w) = K.w ∨
      K.w * j + (if j = K.J - 1 then K.topBits else K.w) = K.L.nbits) at bounds
  have top : k.testBit (K.w * j + (K.w - 1)) = decide (K.H ≤ combWin K.w k j) := testBit_top k K.w j hw.1
  have read : ∀ u : State, Kp [.r6] s u → u.mem = s.mem → K.w * j + K.w ≤ K.L.nbits →
      WP isa (.block K.signRead) u fun t =>
        t.gpr .r10 = (if K.H ≤ combWin K.w k j then 0 else BitVec.allOnes 64) ∧
          Kp [.r4, .r6, .r10] s t ∧ t.mem = s.mem := by
    intro u ku mu hr
    refine WP.mono (signRead_ok K (j := j) (b := k.testBit (K.w * j + (K.w - 1))) (ku.ws hs) (ku.at h3) hw ho
      (by omega) (by rw [ku.g]; exact gj) ?_) fun t ⟨val, kt, mt⟩ => ⟨?_, (ku.mono (by decide)).trans
        (kt.mono (by decide)), mt.trans mu⟩
    · rw [mu, show K.L.bits + K.w * j + K.w - 1 = K.L.bits + (K.w * j + (K.w - 1)) by omega]
      exact hb _ (by omega)
    · rw [val, top]
      by_cases h : K.H ≤ combWin K.w k j <;> simp [h]
  unfold TCombCfg.signMask
  by_cases shortTop : K.topBits < K.w
  · simp only [shortTop, ↓reduceIte]
    rw [WP.seq_iff]
    refine WP.mono (lastTest_ok K (j := j) (by omega) (by omega) gj) fun u ⟨zero, ku, mu⟩ => ?_
    by_cases last : j = K.J - 1
    · refine WP.ite true (by rw [zero]; simp [last]) (fun _ => ?_) (fun hf => by cases hf)
      have e : K.w * j + K.topBits = K.L.nbits := by
        rw [last]; exact Nat.add_sub_of_le start
      have hfalse : k.testBit (K.w * j + (K.w - 1)) = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq,
          Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by omega)))]
        decide
      have high : ¬ K.H ≤ combWin K.w k j := fun h => by
        rw [top, decide_eq_true h] at hfalse; cases hfalse
      refine wp_step (exec_li (by decide)) ?_
      refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ?_)
      simp only [write_gpr, write_mem, ite_true]
      rw [ite_eq_right_of_eq_false _ _ (eq_false high)]
      exact ⟨by decide, (ku.mono (by decide)).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))),
        mu⟩
    · refine WP.ite false (by rw [zero]; simp [last]) (fun ht => by cases ht) (fun _ => ?_)
      exact read u ku mu (by simpa only [last, ↓reduceIte] using bounds.2.1)
  · simp only [shortTop, ↓reduceIte]
    apply read s (Kp.refl _ _) rfl
    have cw : K.w ≤ (if j = K.J - 1 then K.topBits else K.w) := by split <;> omega
    omega

end VG.Proof.Weierstrass.PPC64LE.TComb
