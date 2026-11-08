module

public import VerifiedGarbage.Proof.Variants.Sha256.X86.Scalar
public import VerifiedGarbage.Proof.Variants.Sha256.X86.ShaNi

/-! # The implementations of `Sha256` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.Sha256.X86

def scalar : Proof.Sha256.X86.Variants.Backend := Proof.Variants.Sha256.X86.Scalar.variant

def shaNi : Proof.Sha256.X86.Variants.Backend := Proof.Variants.Sha256.X86.ShaNi.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [shaNi, scalar]

end VG.Proof.Variants.Sha256.X86
