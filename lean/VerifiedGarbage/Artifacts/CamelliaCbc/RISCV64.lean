module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CBC on RISC-V -/

namespace VG.Artifacts.CamelliaCbc.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Camellia.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Camellia.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Camellia.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Camellia.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCbc.RISCV64
