module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha1
public import VerifiedGarbage.Proof.Sha1.AArch64.ScalarBackend

/-! # SHA-1 on AArch64 -/

@[expose] public section

namespace VG.Variants.MdHash.AArch64.Sha1

def variant : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha1.variant Proof.Sha1.AArch64.Scalar.backend

end VG.Variants.MdHash.AArch64.Sha1
