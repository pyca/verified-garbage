module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder

/-! Curves of prime order also supply it (`PrimeOrder`, every point but the
point at infinity has order `n`, and `KilledByN`, `[n]P = O` for every
point), for the proofs that need it. This proof-only interface leaves
contracts and the TCB unchanged. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

/-- The group law of `C`, the soundness of the inversions, and that `C` has
prime order `n`, which kills every point: the variant of a prime-order
curve's interface on x86-64 (`Variants/<Curve>/X86_64/Law.lean`, see
`TCB/Emit.lean`). -/
structure HasLawInvOrd (C : Spec.Weierstrass.Curve) extends HasLawInv C where
  prime : PrimeOrder C
  killed : KilledByN C

end VG.Proof.Weierstrass.X86_64
