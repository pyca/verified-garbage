module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Tier
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha1ShaNi
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256ShaNi

/-!
# The hash functions on x86-64 with the SHA extensions

SHA-1's and SHA-256's compression functions with the SHA extensions,
SHA-512's in scalar code, for a CPU with the SHA extensions but without
AVX2.

A variant of `MdHashTier` on x86-64 (see `TCB/Emit.lean` and
`Proof/Pbkdf2/Md/X86_64/Tier.lean`).
-/

@[expose] public section

namespace VG.Variants.MdHashTier.X86_64.ShaNi

def variant : Proof.Pbkdf2.Md.X86_64.Tier := Proof.Pbkdf2.Md.X86_64.Tier.of "_shani" Proof.Variants.MdHash.X86_64.Sha1ShaNi.compress
  Proof.Variants.MdHash.X86_64.Sha256ShaNi.compress Proof.Sha512.X86_64.Compress.scalar

end VG.Variants.MdHashTier.X86_64.ShaNi
