module

public import VerifiedGarbage.Proof.Sha512.AArch64.Sha3Backend
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512

/-! # SHA-384 on AArch64 -/

@[expose] public section

namespace VG.Variants.MdHash.AArch64.Sha384Sha3

def variant : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha384 Proof.Sha512.AArch64.Sha3.backend

end VG.Variants.MdHash.AArch64.Sha384Sha3
