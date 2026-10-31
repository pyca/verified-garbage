module

public import VerifiedGarbage.Proof.Variants.Sha256.X86.ShaNi

/-! # SHA-256 on x86 with the SHA extensions -/

@[expose] public section

namespace VG.Variants.Sha256.X86.ShaNi

def variant : Proof.Sha256.X86.Variants.Backend := Proof.Variants.Sha256.X86.ShaNi.variant

end VG.Variants.Sha256.X86.ShaNi
