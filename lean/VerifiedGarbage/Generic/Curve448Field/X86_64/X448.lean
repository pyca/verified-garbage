module

public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X448.X86_64.Lit
public import VerifiedGarbage.Proof.X448.X86_64.Instances

/-! X448 and Ed448 share the selected Curve448 exponentiation backend. -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.X448

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.X448.x448Api.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    notes := ["Uses the selected Curve448 field backend \
      throughout the ladder and inversion. The shared exponentiation chain is a call to the \
      matching `vg_gf448_r64_pow223` variant. Callee-saved registers are kept in `scratch`."]
    code := Proof.X448.X86_64.code v
    stack := 8
    verified := Proof.X448.X86_64.code_verified v }]

end VG.Generic.Curve448Field.X86_64.X448
