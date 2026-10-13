module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Ed448.X86_64.PowVariant

/-! Shared Curve448 exponentiation follows the callers' field backend. -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Gf448R64

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  { Spec.X448.Field64.pow223Api with
    target := X86_64.target
    name := v.powName
    features := v.features
    doc := Spec.X448.Field64.pow223Api.doc (notes := ["Uses the selected Curve448 field backend. \
      Saves `rbx`, `rbp` and `r12`–`r15` at bytes 1472–1519 of `ws`, runs the shared \
      addition chain on slot 12, and restores those registers. Squaring runs use public loop counters."])
    code := v.powFn
    contract := Spec.X448.Field64.pow223Contract X86_64.abi
    verified := Proof.Ed448.X86_64.FieldVariant.pow_verified v
    spSafe := Code.all_of_allInstrs (by cases v <;> lit_decide) }]

end VG.Generic.Curve448Field.X86_64.Gf448R64
