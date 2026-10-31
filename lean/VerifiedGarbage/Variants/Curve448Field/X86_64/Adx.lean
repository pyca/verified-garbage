module

public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant

/-! # Curve448's ADX field backend, propagated to every generic caller -/

@[expose] public section

namespace VG.Variants.Curve448Field.X86_64.Adx

def variant : Impl.Ed448.X86_64.FieldVariant := .adx

end VG.Variants.Curve448Field.X86_64.Adx
