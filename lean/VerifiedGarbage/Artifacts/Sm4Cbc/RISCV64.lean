module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
public import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit

/-! # SM4-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Sm4.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Sm4.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.Sm4Cbc.RISCV64
