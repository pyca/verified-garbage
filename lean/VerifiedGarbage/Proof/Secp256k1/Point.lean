import VerifiedGarbage.Spec.Secp256k1

/-!
# secp256k1's base point is on the curve

Evaluated by the kernel; it needs none of the algebra of `Curve.lean`, so the
proofs of the code can use it.
-/

namespace VG.Proof.Secp256k1

open Spec.Weierstrass

theorem onCurve_G : onCurve Spec.Secp256k1.curve (G Spec.Secp256k1.curve) = true := by
  decide +kernel

end VG.Proof.Secp256k1
