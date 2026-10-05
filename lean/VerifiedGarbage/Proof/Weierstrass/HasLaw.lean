import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.InvToM

/-!
# What the proofs of a curve's functions take from its variant

The facts whose proofs need Mathlib's algebra, which only the variant files
(`Variants/<Curve>/<Target>/Law.lean`) import: the curve's group law (`Law`)
and the last step of an inversion by divsteps (`InvToM`, for the AArch64
inversions modulo `p` and `n`). The registration files are generic over them.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

/-- The group law of `C` and the inversions' last step, as a value: the
variant of a curve's interface on each target
(`Variants/<Curve>/<Target>/Law.lean`, see `TCB/Emit.lean`), whose type must
be a `Type`, as the emitter lists the variants. -/
structure HasLaw (C : Curve) : Type where
  law : Law C
  inv : InvToM

end VG.Proof.Weierstrass
