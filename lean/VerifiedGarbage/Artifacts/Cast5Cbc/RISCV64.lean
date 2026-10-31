module

public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit

/-! # CAST5-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact RISCV64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.RISCV64.cbcEncryptChained
    stack := 128
    verified := Proof.Cast5.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.Cast5.cbcDecryptChainedApi.artifact RISCV64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.RISCV64.cbcDecryptChained
    stack := 128
    verified := Proof.Cast5.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.Cast5Cbc.RISCV64
