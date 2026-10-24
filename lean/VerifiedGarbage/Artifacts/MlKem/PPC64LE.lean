module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Ntt
public import VerifiedGarbage.Proof.MlKem.PPC64LE.NttInv
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Mul
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Cbd2
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Encode12
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Decode12
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CheckEk
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CompressEncode
public import VerifiedGarbage.Proof.MlKem.PPC64LE.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KeyGenCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM (FIPS 203) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlKem.PPC64LE

def artifacts : List Artifact := [
  Spec.MlKem.sampleNTTApi.artifact PPC64LE.target {
    notes := ["The function has no stack frame of its own: it saves `r29`–`r31` and its return address in \
        `scratch`; the SHA-3 functions it calls use the 48 bytes of stack below the stack pointer."]
    code := Impl.MlKem.PPC64LE.sampleNTT
    stack := 48
    verified := Proof.MlKem.PPC64LE.Sample.verified },
  Spec.MlKem.nttApi.artifact PPC64LE.target {
    notes := ["The function uses no stack: it saves `r14` and `r15` in `scratch`."]
    code := Impl.MlKem.PPC64LE.ntt
    verified := Proof.MlKem.PPC64LE.Ntt.verified },
  Spec.MlKem.nttInvApi.artifact PPC64LE.target {
    notes := ["The function uses no stack: it saves `r14` and `r15` in `scratch`."]
    code := Impl.MlKem.PPC64LE.nttInv
    verified := Proof.MlKem.PPC64LE.NttInv.verified },
  Spec.MlKem.mulApi.artifact PPC64LE.target {
    notes := ["The function uses no stack: it saves `r14` and `r15` in `scratch`."]
    code := Impl.MlKem.PPC64LE.multiplyNTTs
    verified := Proof.MlKem.PPC64LE.Mul.verified },
  Spec.MlKem.addApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.add
    verified := Proof.MlKem.PPC64LE.Add.add_verified },
  Spec.MlKem.subApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.sub
    verified := Proof.MlKem.PPC64LE.Add.sub_verified },
  Spec.MlKem.cbd2Api.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.cbd2
    verified := Proof.MlKem.PPC64LE.Cbd2.verified },
  Spec.MlKem.encode12Api.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.encode12
    verified := Proof.MlKem.PPC64LE.Encode12.verified },
  Spec.MlKem.decode12Api.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.decode12
    verified := Proof.MlKem.PPC64LE.Decode12.verified },
  Spec.MlKem.compressEncodeApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.compressEncode
    verified := Proof.MlKem.PPC64LE.CompressEncode.verified },
  Spec.MlKem.decodeDecompressApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.decodeDecompress
    verified := Proof.MlKem.PPC64LE.DecodeDecompress.verified },
  Spec.MlKem.keyGenApi.artifact PPC64LE.target {
    notes := ["The function has no stack frame of its own: it saves `r24`–`r31` and its return address in \
        `scratch`; the functions it calls use the 48 bytes of stack below the stack pointer."]
    code := Impl.MlKem.PPC64LE.keygen
    stack := 48
    verified := Proof.MlKem.PPC64LE.KeyGen.verified },
  Spec.MlKem.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.checkEk
    verified := Proof.MlKem.PPC64LE.CheckEk.verified }]

end VG.Artifacts.MlKem.PPC64LE
