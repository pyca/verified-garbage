module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on PPC64LE: signing messages -/

@[expose] public section

namespace VG.Artifacts.MlDsaSignMessage.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign44Api.name
      Impl.MlDsa.PPC64LE.Sign.sign44 Spec.MlDsa.mlDsa44
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.signMessage44_verified },
  Spec.MlDsa.signMessage65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign65Api.name
      Impl.MlDsa.PPC64LE.Sign.sign65 Spec.MlDsa.mlDsa65
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.signMessage65_verified },
  Spec.MlDsa.signMessage87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign87Api.name
      Impl.MlDsa.PPC64LE.Sign.sign87 Spec.MlDsa.mlDsa87
    stack := 96
    verified := Proof.MlDsa.PPC64LE.Message.signMessage87_verified }]

end VG.Artifacts.MlDsaSignMessage.PPC64LE
