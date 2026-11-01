module

public import VerifiedGarbage.Proof.MlKem1024.X86.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.X86.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.X86.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.X86.Encaps
public import VerifiedGarbage.Proof.MlKem1024.X86.Decaps
import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.MlKem1024.X86.DecodeDecompress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-1024 (FIPS 203) on x86 -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.X86

def artifacts : List Artifact := [
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
