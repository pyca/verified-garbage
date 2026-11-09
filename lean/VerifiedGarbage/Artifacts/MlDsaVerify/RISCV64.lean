module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-DSA (FIPS 204) verification on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlDsaVerify.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.verify44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify44
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.verify44_verified },
  Spec.MlDsa.verify65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify65
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.verify65_verified },
  Spec.MlDsa.verify87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Verify.verify87
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.verify87_verified }]

end VG.Artifacts.MlDsaVerify.RISCV64
