module

public import VerifiedGarbage.Proof.MlKem.X86.CheckEk
public import VerifiedGarbage.Proof.MlKem.X86.KeyGen
public import VerifiedGarbage.Proof.MlKem.X86.Encaps
public import VerifiedGarbage.Proof.MlKem.X86.Decaps
import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.MlKem.X86.AddSub
public import VerifiedGarbage.Proof.MlKem.X86.Cbd
public import VerifiedGarbage.Proof.MlKem.X86.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86.Decode12
public import VerifiedGarbage.Proof.MlKem.X86.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.X86.Encode12
public import VerifiedGarbage.Proof.MlKem.X86.Mul
public import VerifiedGarbage.Proof.MlKem.X86.NttInv
public import VerifiedGarbage.Proof.MlKem.X86.Sample
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ML-KEM (FIPS 203) on x86

The functions that call no other one save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
`vg_mlkem_sample_ntt` also calls the Keccak functions, each in a frame of its
6 arguments (24 bytes), with the return address and the callee's 12 bytes
below it (`stack := 56`). `vg_mlkem768_keygen`, `vg_mlkem768_encaps` and
`vg_mlkem768_decaps` save their caller's registers in 16 bytes, and call
`vg_mlkem_sample_ntt` in a frame of its 3 arguments (12 bytes), with the
return address and the callee's 56 bytes below it (`stack := 88`); their
other calls use less.
-/

@[expose] public section

namespace VG.Artifacts.MlKem.X86

def artifacts : List Artifact := [
  Spec.MlKem.addApi.artifact X86.target {
    code := Impl.MlKem.X86.add
    stack := 16
    verified := Proof.MlKem.X86.add_verified },
  Spec.MlKem.subApi.artifact X86.target {
    code := Impl.MlKem.X86.sub
    stack := 16
    verified := Proof.MlKem.X86.sub_verified },
  Spec.MlKem.encode12Api.artifact X86.target {
    code := Impl.MlKem.X86.encode12
    stack := 16
    verified := Proof.MlKem.X86.Encode12.verified },
  Spec.MlKem.decode12Api.artifact X86.target {
    code := Impl.MlKem.X86.decode12
    stack := 16
    verified := Proof.MlKem.X86.Decode12.verified },
  Spec.MlKem.cbd2Api.artifact X86.target {
    code := Impl.MlKem.X86.cbd2
    stack := 16
    verified := Proof.MlKem.X86.Cbd.verified },
  Spec.MlKem.compressEncodeApi.artifact X86.target {
    code := Impl.MlKem.X86.compressEncode
    stack := 16
    verified := Proof.MlKem.X86.CompressEncode.verified },
  Spec.MlKem.decodeDecompressApi.artifact X86.target {
    code := Impl.MlKem.X86.decodeDecompress
    stack := 16
    verified := Proof.MlKem.X86.DecodeDecompress.verified },
  Spec.MlKem.nttApi.artifact X86.target {
    code := Impl.MlKem.X86.ntt
    stack := 16
    verified := Proof.MlKem.X86.NttFwd.verified },
  Spec.MlKem.nttInvApi.artifact X86.target {
    code := Impl.MlKem.X86.nttInv
    stack := 16
    verified := Proof.MlKem.X86.NttInvP.verified },
  Spec.MlKem.mulApi.artifact X86.target {
    code := Impl.MlKem.X86.multiplyNTTs
    stack := 16
    verified := Proof.MlKem.X86.Mul.verified },
  Spec.MlKem.checkEkApi.artifact X86.target {
    code := Impl.MlKem.X86.checkEk
    stack := 16
    verified := Proof.MlKem.X86.CheckEk.verified },
  Spec.MlKem.sampleNTTApi.artifact X86.target {
    code := Impl.MlKem.X86.sampleNTT
    stack := 56
    verified := Proof.MlKem.X86.Sample.verified },
  Spec.MlKem.keyGenApi.artifact X86.target {
    code := Impl.MlKem.X86.keyGen
    stack := 88
    verified := Proof.MlKem.X86.KeyGen.verified },
  Spec.MlKem.encapsApi.artifact X86.target {
    code := Impl.MlKem.X86.encaps
    stack := 88
    verified := Proof.MlKem.X86.Encaps.verified },
  Spec.MlKem.decapsApi.artifact X86.target {
    code := Impl.MlKem.X86.decaps
    stack := 88
    verified := Proof.MlKem.X86.Decaps.verified }]

end VG.Artifacts.MlKem.X86
