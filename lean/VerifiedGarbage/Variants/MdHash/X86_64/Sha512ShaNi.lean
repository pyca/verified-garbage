module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512

/-! # SHA-512 on x86-64 with the SHA512 extension -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha512ShaNi

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512 .shani (Proof.Pbkdf2.Md.X86_64.Sha512.stream .shani)

end VG.Variants.MdHash.X86_64.Sha512ShaNi
