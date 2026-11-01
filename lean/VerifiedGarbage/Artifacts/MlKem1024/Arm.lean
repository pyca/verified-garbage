module

public import VerifiedGarbage.Proof.MlKem1024.Arm.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.Arm.KeyGenCT
public import VerifiedGarbage.Proof.MlKem1024.Arm.EncapsCT
public import VerifiedGarbage.Proof.MlKem1024.Arm.DecapsCT
public import VerifiedGarbage.Proof.MlKem1024.Arm.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.Arm.Decompress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-1024 (FIPS 203) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.Arm

def artifacts : List Artifact := [
  Spec.MlKem1024.checkEkApi.artifact Arm.target {
    code := Impl.MlKem1024.Arm.checkEk1024
    verified := Proof.MlKem1024.Arm.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact Arm.target {
    code := Impl.MlKem1024.Arm.keygen1024
    stack := 8
    verified := Proof.MlKem1024.Arm.KeyGen.verified },
  Spec.MlKem1024.encapsApi.artifact Arm.target {
    code := Impl.MlKem1024.Arm.encaps1024
    stack := 8
    verified := Proof.MlKem1024.Arm.Encaps.verified },
  Spec.MlKem1024.decapsApi.artifact Arm.target {
    code := Impl.MlKem1024.Arm.decaps1024
    stack := 8
    verified := Proof.MlKem1024.Arm.Decaps.verified }]

end VG.Artifacts.MlKem1024.Arm
