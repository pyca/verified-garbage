module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # ML-DSA (FIPS 204) on PPC64LE: signing messages, with encoded or prepared private keys -/

@[expose] public section

namespace VG.Artifacts.MlDsaSignMessage.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign44Api.name
      Impl.MlDsa.PPC64LE.Sign.sign44 Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.signMessage44_verified },
  Spec.MlDsa.signMessage65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign65Api.name
      Impl.MlDsa.PPC64LE.Sign.sign65 Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.signMessage65_verified },
  Spec.MlDsa.signMessage87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage Spec.MlDsa.sign87Api.name
      Impl.MlDsa.PPC64LE.Sign.sign87 Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.signMessage87_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44")
      Impl.MlDsa.PPC64LE.Sign.signPrepared44 Spec.MlDsa.mlDsa44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.preparedSignMessage44_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65")
      Impl.MlDsa.PPC64LE.Sign.signPrepared65 Spec.MlDsa.mlDsa65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.preparedSignMessage65_verified },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87")
      Impl.MlDsa.PPC64LE.Sign.signPrepared87 Spec.MlDsa.mlDsa87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Message.preparedSignMessage87_verified }]

end VG.Artifacts.MlDsaSignMessage.PPC64LE
