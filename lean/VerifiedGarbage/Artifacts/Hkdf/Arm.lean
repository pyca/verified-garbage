module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hkdf.Table
import VerifiedGarbage.Proof.Hkdf.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.Hkdf.Arm.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HKDF (RFC 5869) on ARMv7 -/

namespace VG.Artifacts.Hkdf.Arm

open VG.Proof.HmacTable.Arm (vars tables fnsOf)

public def artifacts : List (Artifact Arm.target) := [
  Spec.Hkdf.keyApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := Impl.Hkdf.Arm.Fn.key (fnsOf vars)
    verified := Proof.Hkdf.Arm.Scrub.key_scrubbedV },
  Spec.Hkdf.extractApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := Impl.Hkdf.Arm.Fn.extract (fnsOf vars)
    verified := Proof.Hkdf.Arm.Scrub.extract_scrubbedV },
  Spec.Hkdf.expandApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := Impl.Hkdf.Arm.Fn.expand (fnsOf vars)
    verified := Proof.Hkdf.Arm.Scrub.expand_scrubbedV }]

spec_apis artifacts

end VG.Artifacts.Hkdf.Arm
