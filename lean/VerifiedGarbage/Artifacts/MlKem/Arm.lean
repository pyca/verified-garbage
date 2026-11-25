module

public import VerifiedGarbage.Proof.MlKem.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Target

/-! # ML-KEM (FIPS 203) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.MlKem.Arm

def artifacts : List (Artifact Arm.target) := [
  Spec.MlKem.keyGenApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.keyGen
    verified := Proof.MlKem.Arm.Fn.keyGen
    publicOutOk := Proof.MlKem.Arm.Fn.keyGen_public },
  Spec.MlKem.encapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.encaps
    verified := Proof.MlKem.Arm.Fn.encaps
    publicOutOk := Proof.MlKem.Arm.Fn.encaps_public },
  Spec.MlKem.encapsHApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.encapsH
    verified := Proof.MlKem.Arm.Fn.encapsH
    publicOutOk := Proof.MlKem.Arm.Fn.encapsH_public },
  Spec.MlKem.decapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.decaps
    verified := Proof.MlKem.Arm.Fn.decaps
    publicOutOk := Proof.MlKem.Arm.Fn.decaps_public },
  Spec.MlKem.checkEkApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.checkEk
    verified := Proof.MlKem.Arm.Fn.checkEk },
  Spec.MlKem1024.checkEkApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.checkEk1024
    verified := Proof.MlKem.Arm.Fn.checkEk1024 },
  Spec.MlKem1024.keyGenApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.keyGen1024
    verified := Proof.MlKem.Arm.Fn.keyGen1024
    publicOutOk := Proof.MlKem.Arm.Fn.keyGen1024_public },
  Spec.MlKem1024.encapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.encaps1024
    verified := Proof.MlKem.Arm.Fn.encaps1024
    publicOutOk := Proof.MlKem.Arm.Fn.encaps1024_public },
  Spec.MlKem1024.encapsHApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.encapsH1024
    verified := Proof.MlKem.Arm.Fn.encapsH1024
    publicOutOk := Proof.MlKem.Arm.Fn.encapsH1024_public },
  Spec.MlKem1024.decapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Fn.decaps1024
    verified := Proof.MlKem.Arm.Fn.decaps1024
    publicOutOk := Proof.MlKem.Arm.Fn.decaps1024_public }]

end VG.Artifacts.MlKem.Arm
