module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# Complete point addition and doubling as functions: what every target uses

`Proof/Weierstrass/PointContract.lean` decodes a coordinate `x` as
`x R^(p-2)` (`dec`); the proofs of the code have `toM` (`x R⁻¹`). They agree
when Fermat's little theorem holds in `Fin p` (`Fermat`, `dec_eq`), which
follows from the curve's group law (`fermat_of_law`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Point

open VG VG.Proof.Weierstrass

/-- Fermat's little theorem in `Fin p`. -/
def Fermat (p : Nat) [NeZero p] : Prop := ∀ z : Fin p, z ≠ 0 → z * Spec.Weierstrass.pow z (p - 2) = 1

/-- `R⁻¹` is `R^(p-2)`: `dec` is the proofs' `toM`. -/
theorem dec_eq (C : Impl.Weierstrass.Point.Curve) (h1 : (1 : Fin C.p) ≠ 0) (hF : Fermat C.p)
    (hu : UnitMod C.p C.R) (x : Nat) : C.dec x = toM C.p C.R x := by
  have hr := mul_rinv hu
  have hR : Fin.ofNat C.p C.R ≠ 0 := fun h => h1 (by rw [← hr, h]; grind)
  have hf := hF _ hR
  unfold Impl.Weierstrass.Point.Curve.dec toM
  have : Spec.Weierstrass.pow (Fin.ofNat C.p C.R) (C.p - 2) = rinv C.p C.R := by grind
  rw [this]

/-- Fermat's little theorem in `Fe C`: `1 = (1 Z) Z^(p-2)` (`Law.x_eq` for
the representative `(Z : 0 : Z)` of the pair `(1, 0)`). -/
theorem fermat_of_law {CW : Spec.Weierstrass.Curve} (hL : Law CW) : Fermat CW.p :=
  fun z hz => by
    rw [pow_eq_npow]
    have h : Rep CW (1 * z) (0 * z) z (.affine 1 0) := ⟨hz, rfl, rfl⟩
    have e := hL.x_eq h
    rw [e]; grind

end VG.Proof.Weierstrass.Point
