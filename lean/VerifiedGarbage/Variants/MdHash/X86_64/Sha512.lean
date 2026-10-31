module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512

/-! # SHA-512 on x86-64 -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha512

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512 .scalar (Proof.Pbkdf2.Md.X86_64.Sha512.stream .scalar)

end VG.Variants.MdHash.X86_64.Sha512
