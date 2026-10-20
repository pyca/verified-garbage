module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! Public-key validation inherits every shared RSA Montgomery backend. -/

@[expose] public section
namespace VG.Generic.RsaMont.Arm.Domain
open VG

def artifacts (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.checkPublicApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 176
    code := Proof.Ffdh.Arm.SharedCheckPublic.calledCode b
    verified := Proof.Ffdh.Arm.SharedCheckPublic.called_verified b
    notes := ["ARMv7: public-value range checking and optional subgroup exponentiation \
      retain RSA's three-bit fixed-window schedule. Montgomery preparation, \
      multiplication, and specialized squaring call the shared RSA arithmetic helper."] }]

end VG.Generic.RsaMont.Arm.Domain
