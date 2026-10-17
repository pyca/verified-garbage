module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Tier
public import VerifiedGarbage.Proof.Sha1.AArch64.Sha2Backend
public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2Backend
public import VerifiedGarbage.Proof.Sha512.AArch64.Sha3Backend

/-!
# The hash functions on AArch64 with the SHA-1, SHA-256 and SHA-512 instructions

SHA-1's and SHA-256's compression functions with the SHA-1 and SHA-256
instructions (`sha2`), SHA-512's with the SHA-512 instructions (`sha3`).

A variant of `MdHashTier` on AArch64 (see `TCB/Emit.lean` and
`Proof/Pbkdf2/Md/AArch64/Tier.lean`).
-/

@[expose] public section

namespace VG.Variants.MdHashTier.AArch64.Sha2Sha3

def variant : Proof.Pbkdf2.Md.AArch64.Tier := Proof.Pbkdf2.Md.AArch64.Tier.of "_sha2_sha3" Proof.Sha1.AArch64.Sha2.backend Proof.Sha256.AArch64.Sha2.backend
  Proof.Sha512.AArch64.Sha3.backend

end VG.Variants.MdHashTier.AArch64.Sha2Sha3
