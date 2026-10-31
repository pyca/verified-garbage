module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256

/-! # SHA-224 on x86-64: the scalar compression function -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha224

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha224.variant Proof.Variants.MdHash.X86_64.Sha256.compress

end VG.Variants.MdHash.X86_64.Sha224
