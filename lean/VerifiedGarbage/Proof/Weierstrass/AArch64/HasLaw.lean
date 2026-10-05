import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import Mathlib.Data.Nat.Prime.Defs

/-!
# What the proofs of a curve's functions take from its variant, on AArch64

The facts whose proofs need Mathlib's algebra: the curve's group law (`Law`)
and the inversions by divsteps modulo a prime (`InvSounds`), whose proof
(`InvMain.lean`) needs the divsteps' bound and arithmetic. Only the variant
files (`Variants/<Curve>/AArch64/Law.lean`) prove them, so only they import
that algebra; the registration files are generic over them.
-/

namespace VG.Proof.Weierstrass.AArch64

open Spec.Weierstrass

/-- The inversion by divsteps is sound modulo every prime. -/
def InvSounds : Prop := ∀ {m : Nat} [NeZero m], m.Prime → InvSound m

/-- The group law of `C` and the inversions' soundness, as a value: the
variant of a curve's interface on AArch64 (`Variants/<Curve>/AArch64/Law.lean`,
see `TCB/Emit.lean`), whose type must be a `Type`, as the emitter lists the
variants. -/
structure HasLaw (C : Curve) : Type where
  law : Weierstrass.Law C
  inv : InvSounds

end VG.Proof.Weierstrass.AArch64
