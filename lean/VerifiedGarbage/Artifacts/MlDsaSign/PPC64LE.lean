module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # ML-DSA (FIPS 204) signing on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaSign.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.sign44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Sign.sign44_verified },
  Spec.MlDsa.sign65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.sign65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Sign.sign65_verified },
  Spec.MlDsa.sign87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.sign87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Sign.sign87_verified },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.signPrepared44
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Sign.signPrepared44_verified },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.signPrepared65
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Sign.signPrepared65_verified },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.Sign.signPrepared87
    stack := 240
    verified := Proof.MlDsa.PPC64LE.Sign.signPrepared87_verified }]

end VG.Artifacts.MlDsaSign.PPC64LE
