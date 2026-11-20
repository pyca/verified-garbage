module

public import VerifiedGarbage.Proof.MlKem.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # ML-KEM (FIPS 203) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.MlKem.Arm

def artifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.keyGen
    verified := .scrubbed Proof.MlKem.Arm.Fn.keyGen },
  Spec.MlKem.encapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.encaps
    verified := .scrubbed Proof.MlKem.Arm.Fn.encaps },
  Spec.MlKem.encapsHApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.encapsH
    verified := .scrubbed Proof.MlKem.Arm.Fn.encapsH },
  Spec.MlKem.decapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.decaps
    verified := .scrubbed Proof.MlKem.Arm.Fn.decaps },
  Spec.MlKem.checkEkApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.checkEk
    verified := .scrubbed Proof.MlKem.Arm.Fn.checkEk },
  Spec.MlKem1024.checkEkApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.checkEk1024
    verified := .scrubbed Proof.MlKem.Arm.Fn.checkEk1024 },
  Spec.MlKem1024.keyGenApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.keyGen1024
    verified := .scrubbed Proof.MlKem.Arm.Fn.keyGen1024 },
  Spec.MlKem1024.encapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.encaps1024
    verified := .scrubbed Proof.MlKem.Arm.Fn.encaps1024 },
  Spec.MlKem1024.encapsHApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.encapsH1024
    verified := .scrubbed Proof.MlKem.Arm.Fn.encapsH1024 },
  Spec.MlKem1024.decapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.decaps1024
    verified := .scrubbed Proof.MlKem.Arm.Fn.decaps1024 }]

end VG.Artifacts.MlKem.Arm
