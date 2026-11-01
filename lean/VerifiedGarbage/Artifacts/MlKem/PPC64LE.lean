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
public import VerifiedGarbage.Proof.MlKem.PPC64LE.EncapsCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.DecapsCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM (FIPS 203) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlKem.PPC64LE

def artifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.keygen
    stack := 48
    verified := Proof.MlKem.PPC64LE.KeyGen.verified },
  Spec.MlKem.encapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.encaps
    stack := 48
    verified := Proof.MlKem.PPC64LE.Encaps.verified },
  Spec.MlKem.decapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.decaps
    stack := 48
    verified := Proof.MlKem.PPC64LE.Decaps.verified },
  Spec.MlKem.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.checkEk
    verified := Proof.MlKem.PPC64LE.CheckEk.verified }]

end VG.Artifacts.MlKem.PPC64LE
