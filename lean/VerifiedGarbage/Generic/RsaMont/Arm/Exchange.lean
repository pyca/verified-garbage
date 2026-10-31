module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! Shared-secret exponentiation inherits every shared RSA Montgomery backend. -/

@[expose] public section
namespace VG.Generic.RsaMont.Arm.Exchange
open VG

def artifacts (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.exchangeApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 176
    code := Proof.Ffdh.Arm.SharedExchange.calledCode b
    verified := Proof.Ffdh.Arm.SharedExchange.called_verified b }]

end VG.Generic.RsaMont.Arm.Exchange
