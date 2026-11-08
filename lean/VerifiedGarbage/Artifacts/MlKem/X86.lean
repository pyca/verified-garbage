module

public import VerifiedGarbage.Proof.MlKem.X86.CheckEk
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
public import VerifiedGarbage.Proof.MlKem.X86.CallWipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # ML-KEM (FIPS 203) on x86 -/

@[expose] public section

namespace VG.Artifacts.MlKem.X86

def artifacts : List Artifact := [
  Spec.MlKem.checkEkApi.artifact X86.target {
    code := Impl.MlKem.X86.checkEk
    stack := 16
    verified := Proof.MlKem.X86.CheckEk.verified },
  Spec.MlKem.keyGenApi.artifact X86.target {
    code := Impl.MlKem.X86.Wipe.keyGen
    stack := 120
    verified := Proof.MlKem.X86.Wipe.keyGen_verified },
  Spec.MlKem.encapsApi.artifact X86.target {
    code := Impl.MlKem.X86.Wipe.encaps
    stack := 120
    verified := Proof.MlKem.X86.Wipe.encaps_verified },
  Spec.MlKem.encapsHApi.artifact X86.target {
    code := Impl.MlKem.X86.Wipe.encapsH
    stack := 136
    verified := Proof.MlKem.X86.Wipe.encapsH_verified },
  Spec.MlKem.decapsApi.artifact X86.target {
    code := Impl.MlKem.X86.Wipe.decaps
    stack := 120
    verified := Proof.MlKem.X86.Wipe.decaps_verified }]

end VG.Artifacts.MlKem.X86
