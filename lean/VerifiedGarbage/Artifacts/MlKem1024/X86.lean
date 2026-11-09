module

public import VerifiedGarbage.Proof.MlKem1024.X86.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.X86.CheckEk
import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.MlKem1024.X86.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.X86.CallWipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # ML-KEM-1024 (FIPS 203) on x86 -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.X86

def artifacts : List Artifact := [
  Spec.MlKem1024.checkEkApi.artifact X86.target {
    code := Impl.MlKem1024.X86.checkEk
    stack := 16
    verified := Proof.MlKem1024.X86.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact X86.target {
    code := Impl.MlKem.X86.Wipe.keyGen1024
    stack := 120
    verified := Proof.MlKem.X86.Wipe.keyGen1024_verified },
  Spec.MlKem1024.encapsApi.artifact X86.target {
    code := Impl.MlKem.X86.Wipe.encaps1024
    stack := 120
    verified := Proof.MlKem.X86.Wipe.encaps1024_verified },
  Spec.MlKem1024.encapsHApi.artifact X86.target {
    code := Impl.MlKem.X86.Wipe.encapsH1024
    stack := 136
    verified := Proof.MlKem.X86.Wipe.encapsH1024_verified },
  Spec.MlKem1024.decapsApi.artifact X86.target {
    code := Impl.MlKem.X86.Wipe.decaps1024
    stack := 120
    verified := Proof.MlKem.X86.Wipe.decaps1024_verified }]

end VG.Artifacts.MlKem1024.X86
