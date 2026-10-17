module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Tier
public import VerifiedGarbage.Proof.Variants.Sha1.X86.ShaNi
public import VerifiedGarbage.Proof.Variants.Sha256.X86.ShaNi

/-!
# The hash functions on x86 (32-bit) with the SHA extensions

SHA-1's and SHA-256's compression functions with the SHA extensions (which
need SSSE3 too), the others in scalar code.

A variant of `HmacTier` on x86 (see `TCB/Emit.lean` and
`Proof/Pbkdf2/Whole/X86/Tier.lean`).
-/

@[expose] public section

namespace VG.Variants.HmacTier.X86.ShaNi

def variant : Proof.Pbkdf2.Whole.X86.Tier :=
  Proof.Pbkdf2.Whole.X86.Tier.of "_shani" Proof.Variants.Sha1.X86.ShaNi.variant Proof.Variants.Sha256.X86.ShaNi.variant

end VG.Variants.HmacTier.X86.ShaNi
