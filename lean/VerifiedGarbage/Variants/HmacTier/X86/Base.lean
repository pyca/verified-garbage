module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Tier
public import VerifiedGarbage.Proof.Variants.Sha1.X86.Scalar
public import VerifiedGarbage.Proof.Variants.Sha256.X86.Scalar

/-!
# The baseline hash functions on x86 (32-bit)

SHA-1's and SHA-256's compression functions in scalar code (as every other),
for a CPU without the SHA extensions.

A variant of `HmacTier` on x86 (see `TCB/Emit.lean` and
`Proof/Pbkdf2/Whole/X86/Tier.lean`).
-/

@[expose] public section

namespace VG.Variants.HmacTier.X86.Base

def variant : Proof.Pbkdf2.Whole.X86.Tier :=
  Proof.Pbkdf2.Whole.X86.Tier.of "" Proof.Variants.Sha1.X86.Scalar.variant Proof.Variants.Sha256.X86.Scalar.variant

end VG.Variants.HmacTier.X86.Base
