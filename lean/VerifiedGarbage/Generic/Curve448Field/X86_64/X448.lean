module

public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X448.X86_64.Lit
public import VerifiedGarbage.Proof.X448.X86_64.Instances
public import VerifiedGarbage.Proof.X448.X86_64.Exchange
public import VerifiedGarbage.TCB.X86_64.Print

/-! # X448 and Ed448 share the selected Curve448 exponentiation backend -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.X448

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.X448.x448Api.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := Proof.X448.X86_64.code v
    stack := 8
    verified := Proof.X448.X86_64.code_verified v },
  Spec.X448.exchangeApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := Impl.Xdh.X86_64.exchange ("vg_x448" ++ v.suffix) (Proof.X448.X86_64.code v) 56
    stack := 24
    verified := Proof.X448.X86_64.Exchange.exchange_variant v },
  Spec.X448.x448BaseApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := Proof.X448.X86_64.codeBase v
    stack := 8
    verified := Proof.X448.X86_64.codeBase_verified v }]

end VG.Generic.Curve448Field.X86_64.X448
