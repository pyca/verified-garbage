module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1

/-! # SHA-1 on x86-64: the scalar compression function -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha1

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Pbkdf2.Md.X86_64.Sha1.variant .scalar

end VG.Variants.MdHash.X86_64.Sha1
