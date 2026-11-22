module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Hkdf.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Hkdf.Arm.Fn

/-! # HKDF (RFC 5869) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Hkdf.Arm

open VG.Proof.HmacTable.Arm (vars tables fnsOf)

def artifacts : List Artifact := [
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

end VG.Artifacts.Hkdf.Arm
