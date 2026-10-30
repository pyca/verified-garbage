module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) key generation on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaKeyGen.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.KeyGen.keyGen44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.KeyGen.keyGen65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.KeyGen.keyGen87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.KeyGen.keyGen87_verified }]

end VG.Artifacts.MlDsaKeyGen.PPC64LE
