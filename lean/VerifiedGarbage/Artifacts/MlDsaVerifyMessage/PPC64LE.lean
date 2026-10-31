module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on PPC64LE: verifying messages -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerifyMessage.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.verifyMessage44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.verifyMessage Spec.MlDsa.verify44Api.name
      Impl.MlDsa.PPC64LE.Verify.verify44 Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.verifyMessage44_verified },
  Spec.MlDsa.verifyMessage65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.verifyMessage Spec.MlDsa.verify65Api.name
      Impl.MlDsa.PPC64LE.Verify.verify65 Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.verifyMessage65_verified },
  Spec.MlDsa.verifyMessage87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.verifyMessage Spec.MlDsa.verify87Api.name
      Impl.MlDsa.PPC64LE.Verify.verify87 Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.verifyMessage87_verified }]

end VG.Artifacts.MlDsaVerifyMessage.PPC64LE
