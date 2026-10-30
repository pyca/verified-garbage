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
  Spec.MlKem.sampleNTTApi.artifact Arm.target {
    code := Impl.MlKem.Arm.sampleNTT
    stack := 8
    verified := Proof.MlKem.Arm.Sample.verified },
  Spec.MlKem.nttApi.artifact Arm.target {
    code := Impl.MlKem.Arm.ntt
    verified := Proof.MlKem.Arm.Ntt.verified },
  Spec.MlKem.nttInvApi.artifact Arm.target {
    code := Impl.MlKem.Arm.nttInv
    verified := Proof.MlKem.Arm.NttInv.verified },
  Spec.MlKem.mulApi.artifact Arm.target {
    code := Impl.MlKem.Arm.multiplyNTTs
    verified := Proof.MlKem.Arm.Mul.verified },
  Spec.MlKem.addApi.artifact Arm.target {
    code := Impl.MlKem.Arm.add
    verified := Proof.MlKem.Arm.Add.add_verified },
  Spec.MlKem.subApi.artifact Arm.target {
    code := Impl.MlKem.Arm.sub
    verified := Proof.MlKem.Arm.Add.sub_verified },
  Spec.MlKem.cbd2Api.artifact Arm.target {
    code := Impl.MlKem.Arm.cbd2
    verified := Proof.MlKem.Arm.Cbd2.verified },
  Spec.MlKem.encode12Api.artifact Arm.target {
    code := Impl.MlKem.Arm.encode12
    verified := Proof.MlKem.Arm.Encode12.verified },
  Spec.MlKem.decode12Api.artifact Arm.target {
    code := Impl.MlKem.Arm.decode12
    verified := Proof.MlKem.Arm.Decode12.verified },
  Spec.MlKem.compressEncodeApi.artifact Arm.target {
    code := Impl.MlKem.Arm.compressEncode
    verified := Proof.MlKem.Arm.CompressEncode.verified },
  Spec.MlKem.decodeDecompressApi.artifact Arm.target {
    code := Impl.MlKem.Arm.decodeDecompress
    verified := Proof.MlKem.Arm.Decompress.verified },
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
