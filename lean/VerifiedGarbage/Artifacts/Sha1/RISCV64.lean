module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Sha1.RISCV64.Scrub
import VerifiedGarbage.Impl.Sha1.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SHA-1 (FIPS 180-4) on RISC-V -/

namespace VG.Artifacts.Sha1.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Sha1.initApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Fn.init
    verified := Proof.Sha1.RISCV64.init_scrubbed },
  Spec.Sha1.updateApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Fn.update
    verified := Proof.Sha1.RISCV64.update_scrubbed },
  Spec.Sha1.finalizeApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Fn.finalize
    verified := Proof.Sha1.RISCV64.finalize_scrubbed },
  Spec.Sha1.digestApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Fn.digest
    verified := Proof.Sha1.RISCV64.digest_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sha1.RISCV64
