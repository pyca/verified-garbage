module

public import VerifiedGarbage.Proof.MlKem.Arm.CheckEk
public import VerifiedGarbage.Proof.MlKem.Arm.NttInv
public import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
public import VerifiedGarbage.Proof.MlKem.Arm.CallWipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.MlKem1024.Arm.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.Arm.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.Arm.Decompress

/-! # ML-KEM (FIPS 203) on ARMv7 -/

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
    verified := Proof.MlKem.Arm.CheckEk.verified },
  Spec.MlKem1024.checkEkApi.artifact Arm.target {
    code := Impl.MlKem1024.Arm.checkEk1024
    verified := Proof.MlKem1024.Arm.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Wipe.keyGen1024
    stack := 24
    verified := Proof.MlKem.Arm.Wipe.keyGen1024_verified },
  Spec.MlKem1024.encapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Wipe.encaps1024
    stack := 32
    verified := Proof.MlKem.Arm.Wipe.encaps1024_verified },
  Spec.MlKem1024.encapsHApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Wipe.encapsH1024
    stack := 32
    verified := Proof.MlKem.Arm.Wipe.encapsH1024_verified },
  Spec.MlKem1024.decapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.Wipe.decaps1024
    stack := 24
    verified := Proof.MlKem.Arm.Wipe.decaps1024_verified }]

end VG.Artifacts.MlKem.Arm
