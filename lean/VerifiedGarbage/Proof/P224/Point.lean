import VerifiedGarbage.Spec.P224

/-!
# P-224's base point is on the curve

Evaluated by the kernel; it needs none of the algebra of `Curve.lean`, so the
proofs of the code can use it.
-/

namespace VG.Proof.P224

open Spec.Weierstrass

theorem onCurve_G : onCurve Spec.P224.curve (G Spec.P224.curve) = true := by
  decide +kernel

end VG.Proof.P224
