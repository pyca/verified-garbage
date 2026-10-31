module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deriving an imported scalar's public value inherits every shared RSA Montgomery backend -/

@[expose] public section
namespace VG.Generic.RsaMont.Arm.DerivePublic
open VG

def artifacts (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.derivePublicApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 176
    code := Proof.Ffdh.Arm.SharedDerive.calledCode b
    verified := Proof.Ffdh.Arm.SharedDerive.called_verified b }]

end VG.Generic.RsaMont.Arm.DerivePublic
