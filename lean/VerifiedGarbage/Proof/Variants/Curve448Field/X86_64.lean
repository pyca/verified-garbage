module

public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant

/-! # The implementations of `Curve448Field` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Curve448Field.X86_64

def adx : Impl.Ed448.X86_64.FieldVariant := .adx

def scalar : Impl.Ed448.X86_64.FieldVariant := .scalar

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [adx, scalar]

end VG.Proof.Variants.Curve448Field.X86_64
