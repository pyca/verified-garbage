module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
public import VerifiedGarbage.Impl.Cast5.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit

/-! # CAST5-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Cast5.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Cast5.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Cast5.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.Cast5Cbc.RISCV64
