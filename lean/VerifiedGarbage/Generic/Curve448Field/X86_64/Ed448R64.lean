module

public import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit

/-! # Ed448's point doubling and affine addition, in radix `2^64`, on x86-64 -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448R64

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Point64 VG.Proof.Ed448.X86_64.Point64
open VG.Spec.Ed448.Point64 (doubleApi addAffineApi doubleContract addAffineContract)

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  doubleApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := v.doubleFn
    verified := Proof.Ed448.X86_64.FieldVariant.double_verified v },
  addAffineApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := v.addFn
    verified := Proof.Ed448.X86_64.FieldVariant.add_verified v }]

end VG.Generic.Curve448Field.X86_64.Ed448R64
