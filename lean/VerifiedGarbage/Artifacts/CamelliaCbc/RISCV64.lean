module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Camellia.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Camellia.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Camellia.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.CamelliaCbc.RISCV64
