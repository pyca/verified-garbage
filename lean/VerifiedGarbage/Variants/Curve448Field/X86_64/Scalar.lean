module

public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant

/-! # Curve448's scalar field backend, propagated to every generic caller -/

@[expose] public section

namespace VG.Variants.Curve448Field.X86_64.Scalar

def variant : Impl.Ed448.X86_64.FieldVariant := .scalar

end VG.Variants.Curve448Field.X86_64.Scalar
