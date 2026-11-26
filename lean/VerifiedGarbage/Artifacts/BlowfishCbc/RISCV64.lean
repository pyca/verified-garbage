module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cbc
import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
import VerifiedGarbage.Impl.Blowfish.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CBC on RISC-V -/

namespace VG.Artifacts.BlowfishCbc.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Blowfish.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Blowfish.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishCbc.RISCV64
