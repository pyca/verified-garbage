module

public import VerifiedGarbage.Proof.MlDsa.X86.PkTr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-! # ML-DSA (FIPS 204) public-key hash `tr = H(pk, 64)` on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.MlDsaPkTr.X86

def artifacts : List Artifact := [
  Spec.MlDsa.pkTr44Api.artifact X86.target {
    code := Impl.MlDsa.X86.PkTr.pkTr Spec.MlDsa.mlDsa44
    stack := 56
    verified := Proof.MlDsa.X86.PkTr.pkTr44_verified },
  Spec.MlDsa.pkTr65Api.artifact X86.target {
    code := Impl.MlDsa.X86.PkTr.pkTr Spec.MlDsa.mlDsa65
    stack := 56
    verified := Proof.MlDsa.X86.PkTr.pkTr65_verified },
  Spec.MlDsa.pkTr87Api.artifact X86.target {
    code := Impl.MlDsa.X86.PkTr.pkTr Spec.MlDsa.mlDsa87
    stack := 56
    verified := Proof.MlDsa.X86.PkTr.pkTr87_verified }]

end VG.Artifacts.MlDsaPkTr.X86
