module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) signing on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaSign.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.sign44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Sign.sign44_verified },
  Spec.MlDsa.sign65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.sign65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Sign.sign65_verified },
  Spec.MlDsa.sign87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.sign87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Sign.sign87_verified }]

end VG.Artifacts.MlDsaSign.PPC64LE
