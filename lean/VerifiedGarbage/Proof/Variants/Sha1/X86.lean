module

public import VerifiedGarbage.Proof.Variants.Sha1.X86.Scalar
public import VerifiedGarbage.Proof.Variants.Sha1.X86.ShaNi

/-! # The implementations of `Sha1` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.Sha1.X86

def scalar : Proof.Sha1.X86.Variants.Backend := Proof.Variants.Sha1.X86.Scalar.variant

def shaNi : Proof.Sha1.X86.Variants.Backend := Proof.Variants.Sha1.X86.ShaNi.variant

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [scalar, shaNi]

end VG.Proof.Variants.Sha1.X86
