module

public import VerifiedGarbage.Proof.Variants.Sha1.X86.ShaNi

/-! # SHA-1 on x86 with the SHA extensions -/

@[expose] public section

namespace VG.Variants.Sha1.X86.ShaNi

def variant : Proof.Sha1.X86.Variants.Backend := Proof.Variants.Sha1.X86.ShaNi.variant

end VG.Variants.Sha1.X86.ShaNi
