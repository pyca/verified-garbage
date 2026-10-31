module

public import VerifiedGarbage.Proof.Sha512.AArch64.Sha3Backend
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512

/-! # SHA-512/256 on AArch64 -/

@[expose] public section

namespace VG.Variants.MdHash.AArch64.Sha512_256Sha3

def variant : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_256 Proof.Sha512.AArch64.Sha3.backend

end VG.Variants.MdHash.AArch64.Sha512_256Sha3
