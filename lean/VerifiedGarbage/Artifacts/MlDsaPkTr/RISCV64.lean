module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PkTr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-DSA (FIPS 204) public-key hash `tr = H(pk, 64)` on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlDsaPkTr.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.pkTr44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PkTr.pkTr Spec.MlDsa.mlDsa44
    stack := 1168
    verified := Proof.MlDsa.RISCV64.PkTr.pkTr44_verified },
  Spec.MlDsa.pkTr65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PkTr.pkTr Spec.MlDsa.mlDsa65
    stack := 1168
    verified := Proof.MlDsa.RISCV64.PkTr.pkTr65_verified },
  Spec.MlDsa.pkTr87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.PkTr.pkTr Spec.MlDsa.mlDsa87
    stack := 1168
    verified := Proof.MlDsa.RISCV64.PkTr.pkTr87_verified }]

end VG.Artifacts.MlDsaPkTr.RISCV64
