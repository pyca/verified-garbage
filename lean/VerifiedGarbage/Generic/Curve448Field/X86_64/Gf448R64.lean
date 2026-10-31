module

public import VerifiedGarbage.Proof.Ed448.X86_64.PowVariant
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X448.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Shared Curve448 exponentiation follows the callers' field backend -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Gf448R64

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.X448.Field64.pow223Api.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := v.powFn
    verified := Proof.Ed448.X86_64.FieldVariant.pow_verified v }]

end VG.Generic.Curve448Field.X86_64.Gf448R64
