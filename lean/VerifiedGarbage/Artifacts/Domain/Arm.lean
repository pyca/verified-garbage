module

public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.Ffdh.Arm
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicInstances
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm

/-! # Emit every native ARMv7 FFDH backend and propagate its exact CPU features -/

@[expose] public section

namespace VG.Artifacts.Domain.Arm.Ffdh
open VG

def artifacts (v : Proof.Ffdh.Arm.Backend) : List Artifact :=
  [Spec.Ffdh.checkDomainApi.artifact VG.Arm.target {
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

end VG.Artifacts.Domain.Arm.Ffdh

-- Public-key validation inherits every shared RSA Montgomery backend
namespace VG.Artifacts.Domain.Arm.RsaMont
open VG

def artifacts (b : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.checkPublicApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 176
    code := Proof.Ffdh.Arm.SharedCheckPublic.calledCode b
    verified := Proof.Ffdh.Arm.SharedCheckPublic.called_verified b }]

end VG.Artifacts.Domain.Arm.RsaMont

namespace VG.Artifacts.Domain.Arm

def artifacts : List Artifact :=
  (VG.Proof.Variants.Ffdh.Arm.variants.flatMap fun v => Ffdh.artifacts v) ++
  (VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => RsaMont.artifacts v)

end VG.Artifacts.Domain.Arm
