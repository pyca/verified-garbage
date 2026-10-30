module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) verification on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.verify44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Verify.verify44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Verify.verify44_verified },
  Spec.MlDsa.verify65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Verify.verify65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Verify.verify65_verified },
  Spec.MlDsa.verify87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Verify.verify87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Verify.verify87_verified }]

end VG.Artifacts.MlDsaVerify.PPC64LE
