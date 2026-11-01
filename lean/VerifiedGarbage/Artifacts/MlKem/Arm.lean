module

public import VerifiedGarbage.Proof.MlKem.Arm.CheckEk
public import VerifiedGarbage.Proof.MlKem.Arm.KeyGenCT
public import VerifiedGarbage.Proof.MlKem.Arm.EncapsCT
public import VerifiedGarbage.Proof.MlKem.Arm.DecapsCT
public import VerifiedGarbage.Proof.MlKem.Arm.NttInv
public import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM (FIPS 203) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlKem.Arm

def artifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact Arm.target {
    code := Impl.MlKem.Arm.keygen
    stack := 8
    verified := Proof.MlKem.Arm.KeyGen.verified },
  Spec.MlKem.encapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.encaps
    stack := 8
    verified := Proof.MlKem.Arm.Encaps.verified },
  Spec.MlKem.decapsApi.artifact Arm.target {
    code := Impl.MlKem.Arm.decaps
    stack := 8
    verified := Proof.MlKem.Arm.Decaps.verified },
  Spec.MlKem.checkEkApi.artifact Arm.target {
    code := Impl.MlKem.Arm.checkEk
    verified := Proof.MlKem.Arm.CheckEk.verified }]

end VG.Artifacts.MlKem.Arm
