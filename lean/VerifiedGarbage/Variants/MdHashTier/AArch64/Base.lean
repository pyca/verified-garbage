module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Tier
public import VerifiedGarbage.Proof.Sha1.AArch64.ScalarBackend
public import VerifiedGarbage.Proof.Sha256.AArch64.ScalarBackend
public import VerifiedGarbage.Proof.Sha512.AArch64.ScalarBackend

/-!
# The baseline hash functions on AArch64

Every compression function in scalar code, for a CPU without the SHA-1 and
SHA-256 instructions.

A variant of `MdHashTier` on AArch64 (see `TCB/Emit.lean` and
`Proof/Pbkdf2/Md/AArch64/Tier.lean`).
-/

@[expose] public section

namespace VG.Variants.MdHashTier.AArch64.Base

def variant : Proof.Pbkdf2.Md.AArch64.Tier := Proof.Pbkdf2.Md.AArch64.Tier.of "" Proof.Sha1.AArch64.Scalar.backend Proof.Sha256.AArch64.Scalar.backend
  Proof.Sha512.AArch64.Scalar.backend

end VG.Variants.MdHashTier.AArch64.Base
