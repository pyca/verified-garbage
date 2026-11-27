module
-- separate module: the proofs of the code on every target import `onCurve_G` without the algebra of `Curve.lean` or the comb tables

public import VerifiedGarbage.Spec.BrainpoolP320r1

/-!
# brainpoolP320r1's base point is on the curve

Evaluated by the kernel; it needs none of the algebra of `Curve.lean`, so the
proofs of the code can use it.
-/

@[expose] public section

namespace VG.Proof.BrainpoolP320r1

open Spec.Weierstrass

theorem onCurve_G : onCurve Spec.BrainpoolP320r1.curve (G Spec.BrainpoolP320r1.curve) = true := by
  decide +kernel

end VG.Proof.BrainpoolP320r1
