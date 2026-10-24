module

public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Framework.Registration

/-! Emit every native ARMv7 FFDH backend and propagate its exact CPU features. -/

@[expose] public section
namespace VG.Generic.Ffdh.Arm.Domain
open VG

def artifacts (v : Proof.Ffdh.Arm.Backend) : List Artifact :=
  [Spec.Ffdh.checkDomainApi.artifact VG.Arm.target {
    consts := Impl.Ffdh.Arm.VettedGroups.tableConsts
    suffix := v.suffix
    features := v.features
    stack := 128
    code := v.checkDomain
    verified := v.checkDomain_verified
    notes := ["ARMv7: exact recognition certifies the ten standard MODP/FFDHE domains. \
      All other parameters use RSA's packed-u64 working space and native 32-bit arithmetic check the \
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
      every supplied private-scalar byte, including leading zeros."] }]

end VG.Generic.Ffdh.Arm.Domain
