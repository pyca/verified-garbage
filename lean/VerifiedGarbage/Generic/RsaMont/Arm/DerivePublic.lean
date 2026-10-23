module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! Deriving an imported scalar's public value inherits every shared RSA Montgomery backend. -/

@[expose] public section
namespace VG.Generic.RsaMont.Arm.DerivePublic
open VG

def artifacts (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.derivePublicApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 176
    code := Proof.Ffdh.Arm.SharedDerive.calledCode b
    verified := Proof.Ffdh.Arm.SharedDerive.called_verified b
    notes := ["ARMv7: the scalar's range is checked as `vg_ffdh_check_private` checks it, the \
      one branch on x. The power of g uses RSA's fixed three-bit windows over every supplied \
      scalar byte, as the exchange does; y's range is the acceptance mask, which clears the \
      output. Powers of a checked generator remain in its q subgroup, so y needs only its \
      range check. Products and squares call the shared RSA arithmetic helper."] }]

end VG.Generic.RsaMont.Arm.DerivePublic
