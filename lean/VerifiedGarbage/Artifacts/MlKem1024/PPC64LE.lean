module

public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CheckEk
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CallWipe
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Decompress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # ML-KEM-1024 (FIPS 203) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.PPC64LE

def artifacts : List Artifact := [
  Spec.MlKem1024.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem1024.PPC64LE.checkEk1024
    verified := Proof.MlKem1024.PPC64LE.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.keyGen1024
    stack := 176
    verified := Proof.MlKem.PPC64LE.Wipe.keyGen1024_verified },
  Spec.MlKem1024.encapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.encaps1024
    stack := 176
    verified := Proof.MlKem.PPC64LE.Wipe.encaps1024_verified },
  Spec.MlKem1024.encapsHApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.encapsH1024
    stack := 176
    verified := Proof.MlKem.PPC64LE.Wipe.encapsH1024_verified },
  Spec.MlKem1024.decapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.decaps1024
    stack := 176
    verified := Proof.MlKem.PPC64LE.Wipe.decaps1024_verified }]

end VG.Artifacts.MlKem1024.PPC64LE
