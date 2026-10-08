import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.PrimeOrder

/-! Curves of prime order also supply it (`PrimeOrder`, every point but the
point at infinity has order `n`), for the proofs that need it. This
proof-only interface leaves contracts and the TCB unchanged. -/
namespace VG.Proof.Weierstrass.X86_64

/-- The group law of `C`, the soundness of the inversions, and that `C` has
prime order: the variant of a prime-order curve's interface on x86-64
(`Variants/<Curve>/X86_64/Law.lean`, see `TCB/Emit.lean`). -/
structure HasLawInvOrd (C : Spec.Weierstrass.Curve) extends HasLawInv C where
  prime : PrimeOrder C

end VG.Proof.Weierstrass.X86_64
