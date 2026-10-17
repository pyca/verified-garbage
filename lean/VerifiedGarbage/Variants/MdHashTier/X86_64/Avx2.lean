module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Tier
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2

/-!
# The hash functions on x86-64 with AVX2

SHA-256's and SHA-512's compression functions with AVX2 (and BMI1 and
BMI2), SHA-1's in scalar code, for a CPU with AVX2 but without the SHA
extensions.

A variant of `MdHashTier` on x86-64 (see `TCB/Emit.lean` and
`Proof/Pbkdf2/Md/X86_64/Tier.lean`).
-/

@[expose] public section

namespace VG.Variants.MdHashTier.X86_64.Avx2

def variant : Proof.Pbkdf2.Md.X86_64.Tier := Proof.Pbkdf2.Md.X86_64.Tier.of "_avx2" Proof.Sha1.X86_64.Compress.scalar
  Proof.Variants.MdHash.X86_64.Sha256Avx2.compress Proof.Sha512.X86_64.Compress.avx2

end VG.Variants.MdHashTier.X86_64.Avx2
