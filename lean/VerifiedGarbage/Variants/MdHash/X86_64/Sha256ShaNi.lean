module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256ShaNi

/-! # SHA-256 on x86-64 with the SHA extensions -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha256ShaNi

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256ShaNi.variant

end VG.Variants.MdHash.X86_64.Sha256ShaNi
