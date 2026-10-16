module

public import VerifiedGarbage.Proof.MlKem1024.X86.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.X86.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.X86.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.X86.Encaps
public import VerifiedGarbage.Proof.MlKem1024.X86.Decaps
import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.MlKem1024.X86.DecodeDecompress
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ML-KEM-1024 (FIPS 203) on x86

The functions that call no other one save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
`vg_mlkem1024_keygen`, `vg_mlkem1024_encaps` and `vg_mlkem1024_decaps` save
their caller's registers in 16 bytes, and call `vg_mlkem_sample_ntt` in a
frame of its 3 arguments (12 bytes), with the return address and the
callee's 56 bytes below it (`stack := 88`); their other calls use less.
-/

@[expose] public section

namespace VG.Artifacts.MlKem1024.X86

def artifacts : List Artifact := [
  Spec.MlKem1024.compressEncodeApi.artifact X86.target {
    code := Impl.MlKem1024.X86.compressEncode
    stack := 16
    verified := Proof.MlKem1024.X86.CompressEncode.verified },
  Spec.MlKem1024.decodeDecompressApi.artifact X86.target {
    code := Impl.MlKem1024.X86.decodeDecompress
    stack := 16
    verified := Proof.MlKem1024.X86.DecodeDecompress.verified },
  Spec.MlKem1024.checkEkApi.artifact X86.target {
    code := Impl.MlKem1024.X86.checkEk
    stack := 16
    verified := Proof.MlKem1024.X86.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact X86.target {
    code := Impl.MlKem1024.X86.keyGen
    stack := 88
    verified := Proof.MlKem1024.X86.KeyGen.verified },
  Spec.MlKem1024.encapsApi.artifact X86.target {
    code := Impl.MlKem1024.X86.encaps
    stack := 88
    verified := Proof.MlKem1024.X86.Encaps.verified },
  Spec.MlKem1024.decapsApi.artifact X86.target {
    code := Impl.MlKem1024.X86.decaps
    stack := 88
    verified := Proof.MlKem1024.X86.Decaps.verified }]

end VG.Artifacts.MlKem1024.X86
