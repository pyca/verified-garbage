module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! X448 and Ed448 share the selected Curve448 exponentiation backend. -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.X448

def code : Impl.Ed448.X86_64.FieldVariant → Prog X86_64.isa
  | .scalar => Impl.X448.X86_64.x448
  | .adx => Impl.X448.X86_64.x448Adx

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.X448.x448Api.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    notes := ["Uses the selected Curve448 field backend \
      throughout the ladder and inversion. The shared exponentiation chain is a call to the \
      matching `vg_gf448_r64_pow223` variant. Callee-saved registers are kept in `scratch`."]
    code := code v
    stack := 8
    verified := by cases v; exact Proof.X448.X86_64.x448_verified; exact Proof.X448.X86_64.x448Adx_verified
    spSafe := Code.all_of_allInstrs (by cases v <;> lit_decide) }]

end VG.Generic.Curve448Field.X86_64.X448
