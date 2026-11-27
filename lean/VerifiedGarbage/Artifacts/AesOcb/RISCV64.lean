module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesOcb.RISCV64.Init
import VerifiedGarbage.Proof.AesOcb.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OCB (RFC 7253) on RISC-V -/

namespace VG.Artifacts.AesOcb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ocb.initApi.artifact RISCV64.target {
    code := Impl.AesOcb.RISCV64.Fn.init
    verified := Proof.AesOcb.RISCV64.init_scrubbed },
  Spec.Ocb.sealApi.artifact RISCV64.target {
    code := Impl.AesOcb.RISCV64.Fn.«seal»
    verified := Proof.AesOcb.RISCV64.Scrub.seal_scrubbed },
  Spec.Ocb.openApi.artifact RISCV64.target {
    code := Impl.AesOcb.RISCV64.Fn.«open»
    verified := Proof.AesOcb.RISCV64.Scrub.open_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesOcb.RISCV64
