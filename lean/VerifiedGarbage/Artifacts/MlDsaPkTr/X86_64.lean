module

public import VerifiedGarbage.Proof.MlDsa.X86_64.PkTr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-! # ML-DSA (FIPS 204) public-key hash `tr = H(pk, 64)` on x86-64 -/

@[expose] public section

namespace VG.Artifacts.MlDsaPkTr.X86_64

def artifacts : List Artifact := [
  Spec.MlDsa.pkTr44Api.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa44
    stack := 32
    verified := Proof.MlDsa.X86_64.PkTr.pkTr44_verified },
  Spec.MlDsa.pkTr65Api.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa65
    stack := 32
    verified := Proof.MlDsa.X86_64.PkTr.pkTr65_verified },
  Spec.MlDsa.pkTr87Api.artifact X86_64.target {
    code := Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa87
    stack := 32
    verified := Proof.MlDsa.X86_64.PkTr.pkTr87_verified }]

end VG.Artifacts.MlDsaPkTr.X86_64
