import VerifiedGarbage.Spec.BrainpoolP512r1

/-!
# brainpoolP512r1's base point is on the curve

Evaluated by the kernel; it needs none of the algebra of `Curve.lean`, so the
proofs of the code can use it.
-/

namespace VG.Proof.BrainpoolP512r1

open Spec.Weierstrass

theorem onCurve_G : onCurve Spec.BrainpoolP512r1.curve (G Spec.BrainpoolP512r1.curve) = true := by
  decide +kernel

end VG.Proof.BrainpoolP512r1
