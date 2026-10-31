module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-CBC artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cbcEncryptChained
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cbcEncryptChained_verified },
  Spec.TripleDes.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cbcDecryptChained
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.TripleDesCbc.RISCV64
