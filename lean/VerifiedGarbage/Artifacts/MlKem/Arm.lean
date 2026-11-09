module

public import VerifiedGarbage.Proof.MlKem.Arm.CheckEk
public import VerifiedGarbage.Proof.MlKem.Arm.NttInv
public import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
public import VerifiedGarbage.Proof.MlKem.Arm.CallWipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # ML-KEM (FIPS 203) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlKem.Arm

def artifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Wipe.keyGen
    stack := 24
    verified := Proof.MlKem.Arm.Wipe.keyGen_verified },
  Spec.MlKem.encapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Wipe.encaps
    stack := 32
    verified := Proof.MlKem.Arm.Wipe.encaps_verified },
  Spec.MlKem.encapsHApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Wipe.encapsH
    stack := 32
    verified := Proof.MlKem.Arm.Wipe.encapsH_verified },
  Spec.MlKem.decapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Wipe.decaps
    stack := 24
    verified := Proof.MlKem.Arm.Wipe.decaps_verified },
  Spec.MlKem.checkEkApi.artifact Arm.target {
    code := Impl.MlKem.Arm.checkEk
    verified := Proof.MlKem.Arm.CheckEk.verified }]

end VG.Artifacts.MlKem.Arm
