module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha1ShaNi

/-! # SHA-1 on x86-64 with the SHA extensions -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha1ShaNi

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha1ShaNi.variant

end VG.Variants.MdHash.X86_64.Sha1ShaNi
