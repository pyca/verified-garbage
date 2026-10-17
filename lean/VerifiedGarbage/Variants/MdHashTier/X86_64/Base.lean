module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Tier
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256

/-!
# The baseline hash functions on x86-64

Every compression function in scalar code, for a CPU without the SHA
extensions or AVX2.

A variant of `MdHashTier` on x86-64 (see `TCB/Emit.lean` and
`Proof/Pbkdf2/Md/X86_64/Tier.lean`).
-/

@[expose] public section

namespace VG.Variants.MdHashTier.X86_64.Base

def variant : Proof.Pbkdf2.Md.X86_64.Tier := Proof.Pbkdf2.Md.X86_64.Tier.of "" Proof.Sha1.X86_64.Compress.scalar Proof.Variants.MdHash.X86_64.Sha256.compress
  Proof.Sha512.X86_64.Compress.scalar

end VG.Variants.MdHashTier.X86_64.Base
