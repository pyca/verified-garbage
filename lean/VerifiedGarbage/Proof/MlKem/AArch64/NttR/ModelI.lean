module

import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Model
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Idx
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
public import VerifiedGarbage.Proof.MlKem.NttLayer

/-!
# ML-KEM on AArch64: the inverse NTT halfword by halfword, its coefficients

The coefficients after each level of `NTT⁻¹` (`Li`: its Gentleman–Sande
layers, the reductions between them and the multiplication by 3303), as the
16-bit inverse NTT (`Impl/MlKem/AArch64/Ntt16.lean`) computes them from the
input's `W`, obey the operations the machine collapses (`modelI`), represent
those of `NTT⁻¹` (`Li_rep`), and their reductions (`Oi`) are the coefficients
of `NTT⁻¹` (`Oi_nttInv`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (LRep gs_lane mm_ok ofNat_zeta zeta_lt nonneg_lane)

/-- The zeta of the block of `p` in `NTT⁻¹`'s layer at distance `len`. -/
def zi (len p : Nat) : Nat := zetaN (256 / len - 1 - p / (2 * len))

/-- The coefficients after `st` levels of `NTT⁻¹`, from the input's `W`. -/
def Li (W : Nat → BitVec 16) : Nat → Nat → BitVec 16
  | 0, p => W p
  | st + 1, p =>
    if invRed st = true then n1W (Li W st p)
    else if st = invScale then mmW (Li W st p) 3303 (twN 3303)
    else if p % (2 * invLen st) < invLen st then Li W st p + Li W st (p + invLen st)
    else mmW (Li W st p - Li W st (p - invLen st)) (zi (invLen st) p) (twN (zi (invLen st) p))

/-- The reduced coefficients after the ten levels. -/
def Oi (W : Nat → BitVec 16) (p : Nat) : BitVec 16 := normL (Li W invRules.layers p)

theorem Li_succ (W : Nat → BitVec 16) (st p : Nat) : Li W (st + 1) p =
    if invRed st = true then n1W (Li W st p)
    else if st = invScale then mmW (Li W st p) 3303 (twN 3303)
    else if p % (2 * invLen st) < invLen st then Li W st p + Li W st (p + invLen st)
    else mmW (Li W st p - Li W st (p - invLen st)) (zi (invLen st) p) (twN (zi (invLen st) p)) := rfl

theorem modelI (W : Nat → BitVec 16) : Model (Li W) (Oi W) invRules := by
  refine ⟨by decide, fun h => absurd h (by decide), fun _ st p p' hg => ?_, fun _ st p p' z t hg hz => ?_,
    fun _ st p hr => ?_, fun _ p => ?_, fun p _ => rfl⟩
  · unfold gsPair at hg
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hg
    obtain ⟨⟨⟨hpos, rfl⟩, hm⟩, -⟩ := hg
    obtain ⟨-, hr, hs⟩ := invLen_pos hpos
    rw [Li_succ, ite_eq_right (by rw [hr]; decide), ite_eq_right hs, ite_eq_left hm]
  · unfold gsPair at hg
    unfold gsZeta at hz
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hg hz
    obtain ⟨⟨⟨hpos, rfl⟩, hm⟩, -⟩ := hg
    obtain ⟨rfl, rfl⟩ := hz
    obtain ⟨-, hr, hs⟩ := invLen_pos hpos
    rw [Li_succ, ite_eq_right (by rw [hr]; decide), ite_eq_right hs]
    generalize invLen st = len at hpos hm ⊢
    have h1 : (p + len) % (2 * len) = p % (2 * len) + len := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show len < 2 * len by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [ite_eq_right (by omega), Nat.add_sub_cancel]
    rfl
  · rw [Li_succ, ite_eq_left hr]
  · rw [Li_succ, ite_eq_right (by decide), ite_eq_left rfl]

/-! ## The coefficients represent `NTT⁻¹`'s -/

/-- The layers of `NTT⁻¹` before level `st`. -/
def jI (st : Nat) : Nat := [0, 1, 2, 3, 3, 4, 5, 6, 6, 7, 7].getD st 7

/-- The bound of the coefficients after level `st`. -/
def bI (st : Nat) : Nat := [3329, 6658, 13316, 26632, 3329, 6658, 13316, 26632, 3329, 6658, 3329].getD st 0

/-- Coefficient `p` of `NTT⁻¹` of `F` after level `st`. -/
def vI (F : Poly) (st p : Nat) : Zq :=
  if st = 10 then (nttInvL 7 F)[p]! * 3303 else (nttInvL (jI st) F)[p]!

/-- A lane reduced to less than `q` in absolute value. -/
theorem n1W_rep {a : BitVec 16} {X : Zq} {B : Nat} (h : LRep a X B) (hB : B ≤ 32768) : LRep (n1W a) X 3329 := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨T, hT, b1, b2, b3⟩ := mm_ok a (z := 1) (by omega) (by decide)
  have e1 : n1W a = a - T * BitVec.ofNat 16 3329 := by
    unfold n1W qdW
    rw [show (BitVec.ofNat 16 10) = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw 1) from rfl, hT]
    rfl
  rw [show a * BitVec.ofNat 16 1 = a from BitVec.mul_one _] at b1 b2 b3
  rw [e1]
  refine ⟨b1, b2, ?_⟩
  omega

/-- A lane times `z`, modulo `q`. -/
theorem mmW_rep {a : BitVec 16} {X : Zq} {B z : Nat} (h : LRep a X B) (hB : B ≤ 32768) (hz : z < 3329) :
    LRep (mmW a z (twN z)) (X * ofNat z) 3329 := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨T, hT, b1, b2, b3⟩ := mm_ok a (z := z) (by omega) hz
  rw [mmW_eq hT]
  refine ⟨b1, b2, ?_⟩
  have e : (X * ofNat z).val = X.val * z % 3329 := by
    rw [val_mul, val_ofNat, Nat.mod_eq_of_lt (show z < q from hz)]
  rw [e]
  generalize a * BitVec.ofNat 16 z - T * BitVec.ofNat 16 3329 = r at b1 b2 b3 ⊢
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero a3
  have : a.toInt * z = X.val * z + 3329 * (k * z) := by rw [show a.toInt = X.val + 3329 * k by omega]; grind
  rw [this] at b3
  generalize a.toInt * z = A at b3
  generalize k * (z : Int) = K at b3
  omega

/-- The facts about the levels with a layer. -/
theorem gs_layers : ∀ st < 10, invRed st = false → st ≠ invScale →
    0 < invLen st ∧ invLen st = 2 <<< jI st ∧ jI (st + 1) = jI st + 1 ∧ jI st < 7 := by decide

theorem gs_bounds : ∀ st < 10, invRed st = false → st ≠ invScale →
    bI (st + 1) = 2 * bI st ∧ 2 * bI st ≤ 32768 ∧ 3329 ≤ 2 * bI st ∧ st + 1 ≠ 10 := by decide

theorem gs_lens : ∀ st < 10, invRed st = false → st ≠ invScale →
    256 / invLen st ≤ 128 ∧ 2 * invLen st * (128 / invLen st) = 256 := by decide

theorem gs_levels {st : Nat} (hs : st < 10) (hr : invRed st = false) (h9 : st ≠ invScale) :
    0 < invLen st ∧ invLen st = 2 <<< jI st ∧ jI (st + 1) = jI st + 1 ∧ jI st < 7 ∧ bI (st + 1) = 2 * bI st ∧
      2 * bI st ≤ 32768 ∧ 3329 ≤ 2 * bI st ∧ st + 1 ≠ 10 ∧ 256 / invLen st ≤ 128 ∧
      2 * invLen st * (128 / invLen st) = 256 :=
  let ⟨a, b, c, d⟩ := gs_layers st hs hr h9
  let ⟨e, f, g, h⟩ := gs_bounds st hs hr h9
  let ⟨i, j⟩ := gs_lens st hs hr h9
  ⟨a, b, c, d, e, f, g, h, i, j⟩

theorem red_levels : ∀ st < 10, invRed st = true →
    jI (st + 1) = jI st ∧ bI (st + 1) = 3329 ∧ bI st ≤ 32768 ∧ st + 1 ≠ 10 := by decide

/-- The coefficients after `st` levels represent those of `NTT⁻¹`. -/
theorem Li_rep (W : Nat → BitVec 16) (F : Poly) (h : ∀ p < 256, LRep (W p) F[p]! 3329) :
    ∀ st ≤ 10, ∀ p < 256, LRep (Li W st p) (vI F st p) (bI st)
  | 0, _, p, hp => h p hp
  | st + 1, hs, p, hp => by
    have ih := Li_rep W F h st (by omega)
    have hv : ∀ p, vI F st p = (nttInvL (jI st) F)[p]! := fun p => by rw [vI, ite_eq_right (by omega)]
    rw [Li_succ]
    by_cases hr : invRed st = true
    · obtain ⟨j1, b1, b0, h10⟩ := red_levels st (by omega) hr
      rw [ite_eq_left hr, vI, ite_eq_right h10, j1, b1, ← hv]
      exact n1W_rep (ih p hp) b0
    rw [ite_eq_right hr]
    by_cases h9 : st = invScale
    · rw [ite_eq_left h9]
      have e9 : st = 9 := h9
      subst e9
      rw [vI, ite_eq_left rfl, show jI 9 = 7 from rfl] at *
      rw [show bI 10 = 3329 from rfl, ← hv]
      exact mmW_rep (ih p hp) (by decide) (show 3303 < 3329 by decide)
    rw [ite_eq_right h9]
    obtain ⟨hpos, hlen, j1, hj, b1, hB, hB', h10, h128, hl⟩ :=
      gs_levels (by omega) (Bool.eq_false_iff.2 hr) h9
    rw [vI, ite_eq_right h10, j1, nttInvL_succ_get F hj hp, ← hlen, b1]
    simp only [← hv]
    generalize invLen st = len at hpos h128 hl ⊢
    by_cases hm : p % (2 * len) < len
    · rw [ite_eq_left hm, ite_eq_left hm]
      have hp' : p + len < 256 := by
        have := pair_lt hpos (show p < 2 * len * (128 / len) by omega) hm; omega
      obtain ⟨_, _, l1, -⟩ := gs_lane (z := 0) (ih p hp) (ih (p + len) hp') (by decide) (by omega)
      rw [← Nat.two_mul] at l1
      exact l1
    · rw [ite_eq_right hm, ite_eq_right hm]
      have hk : 256 / len - 1 - p / (2 * len) < 128 := by
        generalize 256 / len = A at h128
        generalize p / (2 * len) = B
        omega
      obtain ⟨T, hT, -, l2⟩ := gs_lane (ih (p - len) (by omega)) (ih p hp) (zeta_lt hk) (by omega)
      unfold zi
      rw [show zetaN (256 / len - 1 - p / (2 * len)) = Impl.MlKem.AArch64.Ntt16.zeta (256 / len - 1 - p / (2 * len))
        from rfl, mmW_eq hT, ← ofNat_zeta hk]
      exact l2.mono hB'

/-- `a`, less than `q` in absolute value, made nonnegative, is its value. -/
theorem normL_val {x : BitVec 16} {X : Zq} (h : LRep x X 3329) : (normL x).toNat = X.val := by
  obtain ⟨b1, b2, b3⟩ := h
  have hn := nonneg_lane b1 b2
  unfold normL
  rw [show BitVec.ofNat 16 qN = BitVec.ofNat 16 3329 from rfl]
  have hX : X.val < 3329 := X.isLt
  have hv : (x + (x.sshiftRight 15 &&& BitVec.ofNat 16 3329)).toInt = (X.val : Int) := by
    rw [hn]
    split <;> omega
  generalize x + (x.sshiftRight 15 &&& BitVec.ofNat 16 3329) = y at hv ⊢
  rw [BitVec.toInt_eq_toNat_cond] at hv
  split at hv <;> omega

/-- The reduced coefficients are those of `NTT⁻¹`. -/
theorem Oi_nttInv (W : Nat → BitVec 16) (F : Poly) (h : ∀ p < 256, LRep (W p) F[p]! 3329) {p : Nat}
    (hp : p < 256) : (Oi W p).toNat = ((nttInv F)[p]!).val := by
  rw [nttInv_eq_nttInvL, map_mul_get _ (show p < n from hp)]
  exact normL_val (Li_rep W F h 10 (by decide) p hp)

end VG.Proof.MlKem.AArch64.NttR
