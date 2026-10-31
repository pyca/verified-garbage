module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
public import VerifiedGarbage.Proof.Sha256.AArch64.ScalarBackend

/-! # SHA-256 on AArch64 -/

@[expose] public section

namespace VG.Variants.MdHash.AArch64.Sha256

def variant : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha256.variant Proof.Sha256.AArch64.Scalar.backend

end VG.Variants.MdHash.AArch64.Sha256
