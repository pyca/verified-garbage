module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Md5.RISCV64.Scrub
import VerifiedGarbage.Impl.Md5.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # MD5 (RFC 1321) on RISC-V -/

namespace VG.Artifacts.Md5.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Md5.initApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Fn.init
    verified := Proof.Md5.RISCV64.init_scrubbed },
  Spec.Md5.updateApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Fn.update
    verified := Proof.Md5.RISCV64.update_scrubbed },
  Spec.Md5.finalizeApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Fn.finalize
    verified := Proof.Md5.RISCV64.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Md5.RISCV64
