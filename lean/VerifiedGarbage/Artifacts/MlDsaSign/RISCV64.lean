module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Inst
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # ML-DSA (FIPS 204) signing on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlDsaSign.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.sign44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign44
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.sign44_verified },
  Spec.MlDsa.sign65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign65
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.sign65_verified },
  Spec.MlDsa.sign87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.Sign.sign87
    stack := 1184
    verified := Proof.MlDsa.RISCV64.PreparedKey.sign87_verified }]

end VG.Artifacts.MlDsaSign.RISCV64
