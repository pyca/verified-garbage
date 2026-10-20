module

public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Framework.Registration

/-! Emit every native ARMv7 FFDH backend and propagate its exact CPU features. -/

@[expose] public section
namespace VG.Generic.Ffdh.Arm.Domain
open VG

def artifacts (v : Proof.Ffdh.Arm.Backend) : List Artifact :=
  [Spec.Ffdh.checkDomainApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := 128
    code := v.checkDomain
    verified := v.checkDomain_verified
    notes := ["ARMv7: RSA's packed-u64 working space and native 32-bit arithmetic check the \
      modulus, generator, subgroup bound, divisibility and subgroup relation. Exponentiation \
      uses fixed three-bit windows; every selected Montgomery row is verified."] },
  Spec.Ffdh.checkPrivateApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := 128
    code := v.checkPrivate
    verified := v.checkPrivate_verified
    notes := ["ARMv7: scalar bounds, public-value range, subgroup membership and equality with \
      the generator's power run in verified code. RSA's fixed three-bit windows process \
      every supplied private-scalar byte, including leading zeros."] },
  Spec.Ffdh.exchangeApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := 128
    code := v.exchange
    verified := v.exchange_verified
    notes := ["ARMv7: RSA's fixed three-bit window exponentiator computes the shared value; \
      range checking, fixed-width export, and rejection masking stay in verified code. \
      Output is cleared without branching on a degenerate result."] }]

end VG.Generic.Ffdh.Arm.Domain
