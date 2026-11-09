module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.PkTr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # ML-DSA (FIPS 204) public-key hash `tr = H(pk, 64)` on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlDsaPkTr.PPC64LE

def artifacts : List Artifact := [
  Spec.MlDsa.pkTr44Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa44
    stack := 48
    verified := Proof.MlDsa.PPC64LE.PkTr.pkTr44_verified },
  Spec.MlDsa.pkTr65Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa65
    stack := 48
    verified := Proof.MlDsa.PPC64LE.PkTr.pkTr65_verified },
  Spec.MlDsa.pkTr87Api.artifact PPC64LE.target {
    code := Impl.MlDsa.PPC64LE.PkTr.pkTr Spec.MlDsa.mlDsa87
    stack := 48
    verified := Proof.MlDsa.PPC64LE.PkTr.pkTr87_verified }]

end VG.Artifacts.MlDsaPkTr.PPC64LE
