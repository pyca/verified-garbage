module

public import VerifiedGarbage.Proof.Sha512.AArch64.ScalarBackend
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512

/-! # SHA-384 on AArch64 -/

@[expose] public section

namespace VG.Variants.MdHash.AArch64.Sha384

def variant : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha384 Proof.Sha512.AArch64.Scalar.backend

end VG.Variants.MdHash.AArch64.Sha384
