module

public import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Inv
public import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
public import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
public import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
public import VerifiedGarbage.Proof.MlKem.AArch64.Mul
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM on AArch64 -/

@[expose] public section

namespace VG.Artifacts.MlKem.AArch64

def artifacts : List Artifact := [
  Spec.MlKem.addApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.add
    verified := Proof.MlKem.AArch64.add_verified },
  Spec.MlKem.subApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.sub
    verified := Proof.MlKem.AArch64.sub_verified },
  Spec.MlKem.encode12Api.artifact AArch64.target {
    code := Impl.MlKem.AArch64.encode12
    verified := Proof.MlKem.AArch64.Encode12.encode12_verified },
  Spec.MlKem.decode12Api.artifact AArch64.target {
    code := Impl.MlKem.AArch64.decode12
    verified := Proof.MlKem.AArch64.Decode12.decode12_verified },
  Spec.MlKem.cbd2Api.artifact AArch64.target {
    code := Impl.MlKem.AArch64.cbd2
    verified := Proof.MlKem.AArch64.Cbd2.cbd2_verified },
  Spec.MlKem.compressEncodeApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.compressEncode
    verified := Proof.MlKem.AArch64.CE.compressEncode_verified },
  Spec.MlKem.decodeDecompressApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.decodeDecompress
    verified := Proof.MlKem.AArch64.DD.decodeDecompress_verified },
  Spec.MlKem.checkEkApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.checkEk
    verified := Proof.MlKem.AArch64.CheckEk.checkEk_verified },
  Spec.MlKem.mulApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.multiplyNTTs
    verified := Proof.MlKem.AArch64.Mul.mul_verified },
  Spec.MlKem.nttApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.Ntt16.ntt
    verified := Proof.MlKem.AArch64.Ntt16.ntt_verified },
  Spec.MlKem.nttInvApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.Ntt16.nttInv
    verified := Proof.MlKem.AArch64.Ntt16.ntt_inv_verified }]

end VG.Artifacts.MlKem.AArch64
