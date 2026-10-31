module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256

/-! # SHA-256 on x86-64: the scalar compression function -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha256

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256.variant

end VG.Variants.MdHash.X86_64.Sha256
