module

public import VerifiedGarbage.Impl.Weierstrass.CoZ
public import VerifiedGarbage.Proof.Weierstrass.JacCoZ
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-!
# A table of odd multiples by co-Z arithmetic

DBLU of an affine `P` gives `2P` and `P` at one `Z` (`dblu_pts`); ZADDU of
`2P` and `(2m - 1)P` sharing a `Z` gives `(2m + 1)P`, and `2P` at its new `Z`
(`zaddu_pts`), for `m ≤ 7` on a curve of prime order `n > 17`, whose
multiples `(2m - 1)P` and `2P` are then neither equal nor opposite.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.CoZTable
open VG.Impl.Weierstrass VG.Impl.Weierstrass.CoZ VG.Proof.Weierstrass Window5 Spec.Weierstrass

theorem rename_eq (σ : Nat → Nat) (op : FOp) : CoZ.rename σ op = op.rename σ := by
  cases op <;> rfl

theorem dblu_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) (h15 : e 15 = 1) :
    (runOps dblu e 8, runOps dblu e 9, runOps dblu e 10) = dblJF (e 13) (e 14) 1 ∧
      runOps dblu e 5 * (1 * 1) = e 13 * (runOps dblu e 10 * runOps dblu e 10) ∧
      runOps dblu e 4 * (1 * 1 * 1) =
        e 14 * (runOps dblu e 10 * runOps dblu e 10 * runOps dblu e 10) := by
  simp only [dblu, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, h15, dblJF, Prod.mk.injEq]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> grind

theorem zaddu_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    ((runOps zaddu e 8, runOps zaddu e 9, runOps zaddu e 10), (runOps zaddu e 0, runOps zaddu e 1)) =
      zadduF (e 0) (e 1) (e 8) (e 9) (e 10) := by
  simp only [zaddu, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, zadduF]

theorem dblu_out : ∀ op ∈ dblu, op.out < 11 := by decide
theorem zaddu_out : ∀ op ∈ zaddu, op.out < 11 := by decide
theorem dblu_reads : readsOk dblu [13, 14, 15] = true := by decide
theorem zaddu_reads : readsOk zaddu [0, 1, 8, 9, 10] = true := by decide

theorem not_dvd_small {n : Nat} {x : Int} (h1 : -n < x) (h2 : x < n) (h0 : x ≠ 0) :
    ¬ (n : Int) ∣ x := by
  rcases Int.lt_or_gt_of_ne h0 with h | h
  · intro hd
    exact not_dvd_of_pos_lt (n := n) (x := -x) (by omega) (by omega) (Int.dvd_neg.mpr hd)
  · exact not_dvd_of_pos_lt h h2

section
variable {C : Curve} (hC : Law C) (hO : PrimeOrder C) (hn : 17 ≤ C.n)
include hC hO hn

omit hC hn in
theorem two_ne_zero_pt {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (h3 : 3 ≤ C.n) :
    mul 2 P ≠ .infinity := mul_ne_infinity hO hP hP0 (by decide) (by omega)

/-- `(2k+1)P` and `2P` at one `Z` are neither equal nor opposite. -/
theorem coz_x {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity) {k : Nat} (hk : k ≤ 6)
    {X1 Y1 X2 Y2 Z : Fe C} (h1 : InvJ C X1 Y1 Z (mul 2 P)) (h2 : InvJ C X2 Y2 Z (mul (2 * k + 1) P))
    (hz : Z ≠ 0) : X1 - X2 ≠ 0 := by
  intro hx
  have hx' : X1 * (Z * Z) - X2 * (Z * Z) = 0 := by
    have e : X1 * (Z * Z) - X2 * (Z * Z) = (X1 - X2) * (Z * Z) := by grind
    rw [e, hx]; grind
  by_cases hy : Y1 * Z * (Z * Z) - Y2 * Z * (Z * Z) = 0
  · have he := h2.same hC h1 hz hz hx' hy
    have h' : zmul ((2 * k + 1 : Nat) : Int) P = zmul (2 : Nat) P := by
      rw [zmul_natCast, zmul_natCast, he]
    have hd := zmul_dvd hC hO hP hP0 h'
    exact not_dvd_small (n := C.n) (x := ((2 * k + 1 : Nat) : Int) - (2 : Nat)) (by omega)
      (by omega) (by omega) hd
  · have he := h2.opposite hC (hC.onCurve_mul hP _) (hC.onCurve_mul hP _) h1 hz hz hx' hy
    rw [hC.add_mul_mul hP] at he
    exact mul_ne_infinity hO hP hP0 (m := 2 * k + 1 + 2) (by omega) (by omega) he

/-- DBLU of the affine `P`: `2P` at `(8, 9, 10)`, `P` at `(5, 4)` with the same nonzero `Z`. -/
theorem dblu_pts (ha : AM3 C) {P : Point C} (hP : onCurve C P = true) {e : Nat → Fe C}
    (h15 : e 15 = 1) (hj : InvJ C (e 13) (e 14) 1 P) :
    InvJ C (runOps dblu e 8) (runOps dblu e 9) (runOps dblu e 10) (mul 2 P) ∧
      InvJ C (runOps dblu e 5) (runOps dblu e 4) (runOps dblu e 10) P ∧ runOps dblu e 10 ≠ 0 := by
  have hP0 : P ≠ .infinity := fun hh => hC.one_ne_zero ((hj.z_zero_iff hC).mpr hh)
  obtain ⟨hT, h5, h4⟩ := dblu_run e h15
  have j2 := InvJ.dbl' hC ha hP hj hT
  rw [show add P P = mul 2 P by
    rw [show add P P = add (mul 1 P) (mul 1 P) by rw [mul_one_pt], hC.add_mul_mul hP]] at j2
  have hz : runOps dblu e 10 ≠ 0 := fun hh =>
    two_ne_zero_pt hO hP hP0 (by omega) ((j2.z_zero_iff hC).mp hh)
  exact ⟨j2, hj.rescale hC hz hC.one_ne_zero h5 h4 (by grind only), hz⟩

/-- ZADDU of `2P` and `(2k + 1)P` at one `Z`: `(2k + 3)P`, and `2P` at its new `Z`. -/
theorem zaddu_pts (ha : AM3 C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    {k : Nat} (hk : k ≤ 6) {e : Nat → Fe C}
    (hd : InvJ C (e 0) (e 1) (e 10) (mul 2 P)) (hr : InvJ C (e 8) (e 9) (e 10) (mul (2 * k + 1) P))
    (hz : e 10 ≠ 0) :
    InvJ C (runOps zaddu e 8) (runOps zaddu e 9) (runOps zaddu e 10) (mul (2 * (k + 1) + 1) P) ∧
      InvJ C (runOps zaddu e 0) (runOps zaddu e 1) (runOps zaddu e 10) (mul 2 P) ∧
      runOps zaddu e 10 ≠ 0 := by
  have ht := zaddu_run e
  have hx := coz_x hC hO hn hP hP0 hk hd hr hz
  obtain ⟨js, jd⟩ := InvJ.zaddu hC ha (hC.onCurve_mul hP 2) (hC.onCurve_mul hP _) hd hr hz hx
  rw [hC.add_mul_mul hP] at js
  rw [← ht] at js jd
  have js' : InvJ C (runOps zaddu e 8) (runOps zaddu e 9) (runOps zaddu e 10)
      (mul (2 * (k + 1) + 1) P) := by
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega]; exact js
  exact ⟨js', jd, fun hh => mul_ne_infinity hO hP hP0 (m := 2 * (k + 1) + 1) (by omega) (by omega)
    ((js'.z_zero_iff hC).mp hh)⟩

end

end VG.Proof.Weierstrass.CoZTable
