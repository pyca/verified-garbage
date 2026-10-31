module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512

/-! # SHA-512/256 on x86-64 with the SHA512 extension -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha512_256ShaNi

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_256 .shani (Proof.Pbkdf2.Md.X86_64.Sha512.stream512_256 .shani)

end VG.Variants.MdHash.X86_64.Sha512_256ShaNi
