module

public import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.Add
public import VerifiedGarbage.Proof.MlKem.RISCV64.Ntt
public import VerifiedGarbage.Proof.MlKem.RISCV64.NttInv
public import VerifiedGarbage.Proof.MlKem.RISCV64.Mul
public import VerifiedGarbage.Proof.MlKem.RISCV64.Cbd2
public import VerifiedGarbage.Proof.MlKem.RISCV64.Encode12
public import VerifiedGarbage.Proof.MlKem.RISCV64.Decode12
public import VerifiedGarbage.Proof.MlKem.RISCV64.CheckEk
public import VerifiedGarbage.Proof.MlKem.RISCV64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.RISCV64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.RISCV64.KeyGenCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.EncapsCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.DecapsCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM (FIPS 203) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlKem.RISCV64

def artifacts : List Artifact := [
  Spec.MlKem.sampleNTTApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.sampleNTT
    stack := 1168
    verified := Proof.MlKem.RISCV64.Sample.verified },
  Spec.MlKem.nttApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.ntt
    verified := Proof.MlKem.RISCV64.Ntt.verified },
  Spec.MlKem.nttInvApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.nttInv
    verified := Proof.MlKem.RISCV64.NttInv.verified },
  Spec.MlKem.mulApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.multiplyNTTs
    verified := Proof.MlKem.RISCV64.Mul.verified },
  Spec.MlKem.addApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.add
    verified := Proof.MlKem.RISCV64.Add.add_verified },
  Spec.MlKem.subApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.sub
    verified := Proof.MlKem.RISCV64.Add.sub_verified },
  Spec.MlKem.cbd2Api.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.cbd2
    verified := Proof.MlKem.RISCV64.Cbd2.verified },
  Spec.MlKem.encode12Api.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.encode12
    verified := Proof.MlKem.RISCV64.Encode12.verified },
  Spec.MlKem.decode12Api.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.decode12
    verified := Proof.MlKem.RISCV64.Decode12.verified },
  Spec.MlKem.compressEncodeApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.compressEncode
    verified := Proof.MlKem.RISCV64.CompressEncode.verified },
  Spec.MlKem.decodeDecompressApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.decodeDecompress
    verified := Proof.MlKem.RISCV64.DecodeDecompress.verified },
  Spec.MlKem.keyGenApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.keygen
    stack := 1168
    verified := Proof.MlKem.RISCV64.KeyGen.verified },
  Spec.MlKem.encapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.encaps
    stack := 1168
    verified := Proof.MlKem.RISCV64.Encaps.verified },
  Spec.MlKem.decapsApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.decaps
    stack := 1168
    verified := Proof.MlKem.RISCV64.Decaps.verified },
  Spec.MlKem.checkEkApi.artifact RISCV64.target {
    code := Impl.MlKem.RISCV64.checkEk
    verified := Proof.MlKem.RISCV64.CheckEk.verified }]

end VG.Artifacts.MlKem.RISCV64
