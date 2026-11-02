module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Inst
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) key generation on RISC-V -/

@[expose] public section

namespace VG.Artifacts.MlDsaKeyGen.RISCV64

def artifacts : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.KeyGen.keyGen44
    stack := 1168
    verified := Proof.MlDsa.RISCV64.KeyGen.keyGen44_verified },
  Spec.MlDsa.keyGen65Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.KeyGen.keyGen65
    stack := 1168
    verified := Proof.MlDsa.RISCV64.KeyGen.keyGen65_verified },
  Spec.MlDsa.keyGen87Api.artifact RISCV64.target {
    code := Impl.MlDsa.RISCV64.KeyGen.keyGen87
    stack := 1168
    verified := Proof.MlDsa.RISCV64.KeyGen.keyGen87_verified }]

end VG.Artifacts.MlDsaKeyGen.RISCV64
