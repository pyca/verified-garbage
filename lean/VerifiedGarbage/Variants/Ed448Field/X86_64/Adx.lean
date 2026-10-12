module

public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant

/-! Ed448's Adx field backend, propagated to every generic caller. -/

@[expose] public section

namespace VG.Variants.Ed448Field.X86_64.Adx

def variant : Impl.Ed448.X86_64.FieldVariant := .adx

end VG.Variants.Ed448Field.X86_64.Adx
