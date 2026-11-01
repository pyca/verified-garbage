module

public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.KeyGenCT
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.EncapsCT
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.DecapsCT
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Decompress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-1024 (FIPS 203) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlKem1024.PPC64LE

def artifacts : List Artifact := [
  Spec.MlKem1024.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem1024.PPC64LE.checkEk1024
    verified := Proof.MlKem1024.PPC64LE.CheckEk.verified },
  Spec.MlKem1024.keyGenApi.artifact PPC64LE.target {
    code := Impl.MlKem1024.PPC64LE.keygen1024
    stack := 48
    verified := Proof.MlKem1024.PPC64LE.KeyGen.verified },
  Spec.MlKem1024.encapsApi.artifact PPC64LE.target {
    code := Impl.MlKem1024.PPC64LE.encaps1024
    stack := 48
    verified := Proof.MlKem1024.PPC64LE.Encaps.verified },
  Spec.MlKem1024.decapsApi.artifact PPC64LE.target {
    code := Impl.MlKem1024.PPC64LE.decaps1024
    stack := 48
    verified := Proof.MlKem1024.PPC64LE.Decaps.verified }]

end VG.Artifacts.MlKem1024.PPC64LE
