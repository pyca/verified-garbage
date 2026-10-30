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
    verified := v.checkDomain_verified },
  Spec.Ffdh.checkPrivateApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := 128
    code := v.checkPrivate
    verified := v.checkPrivate_verified }]

end VG.Generic.Ffdh.Arm.Domain
