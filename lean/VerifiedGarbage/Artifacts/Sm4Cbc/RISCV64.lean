module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CBC on RISC-V -/

namespace VG.Artifacts.Sm4Cbc.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Sm4.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Sm4.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Sm4.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Cbc.RISCV64
