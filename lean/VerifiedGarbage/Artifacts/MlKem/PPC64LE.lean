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
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CallWipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Decompress

/-! # ML-KEM (FIPS 203) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlKem.PPC64LE

def artifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.keyGen
    stack := 96
    verified := Proof.MlKem.PPC64LE.Wipe.keyGen_verified },
  Spec.MlKem.encapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.encaps
    stack := 96
    verified := Proof.MlKem.PPC64LE.Wipe.encaps_verified },
  Spec.MlKem.encapsHApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.encapsH
    stack := 96
    verified := Proof.MlKem.PPC64LE.Wipe.encapsH_verified },
  Spec.MlKem.decapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.decaps
    stack := 96
    verified := Proof.MlKem.PPC64LE.Wipe.decaps_verified },
  Spec.MlKem.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.checkEk
    verified := Proof.MlKem.PPC64LE.CheckEk.verified },
  Spec.MlKem1024.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem1024.PPC64LE.checkEk1024
    verified := Proof.MlKem1024.PPC64LE.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.keyGen1024
    stack := 96
    verified := Proof.MlKem.PPC64LE.Wipe.keyGen1024_verified },
  Spec.MlKem1024.encapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.encaps1024
    stack := 96
    verified := Proof.MlKem.PPC64LE.Wipe.encaps1024_verified },
  Spec.MlKem1024.encapsHApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.encapsH1024
    stack := 96
    verified := Proof.MlKem.PPC64LE.Wipe.encapsH1024_verified },
  Spec.MlKem1024.decapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Wipe.decaps1024
    stack := 96
    verified := Proof.MlKem.PPC64LE.Wipe.decaps1024_verified }]

end VG.Artifacts.MlKem.PPC64LE
