module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm

/-! # Shared-secret exponentiation inherits every shared RSA Montgomery backend -/

@[expose] public section

namespace VG.Artifacts.Exchange.Arm
open VG

def artifactsFor (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.exchangeApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 176
    code := Proof.Ffdh.Arm.SharedExchange.calledCode b
    verified := Proof.Ffdh.Arm.SharedExchange.called_verified b }]

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Exchange.Arm
