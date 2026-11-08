module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm

/-! # Deriving an imported scalar's public value inherits every shared RSA Montgomery backend -/

@[expose] public section

namespace VG.Artifacts.DerivePublic.Arm
open VG

def artifactsFor (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.derivePublicApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 176
    code := Proof.Ffdh.Arm.SharedDerive.calledCode b
    verified := Proof.Ffdh.Arm.SharedDerive.called_verified b }]

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.DerivePublic.Arm
