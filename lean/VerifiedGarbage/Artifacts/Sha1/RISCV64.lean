module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha1.RISCV64.Scrub
public import VerifiedGarbage.Impl.Sha1.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-1 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha1.RISCV64

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Fn.init
    verified := .scrubbed Proof.Sha1.RISCV64.init_scrubbed },
  Spec.Sha1.updateApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Fn.update
    verified := .scrubbed Proof.Sha1.RISCV64.update_scrubbed },
  Spec.Sha1.finalizeApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Fn.finalize
    verified := .scrubbed Proof.Sha1.RISCV64.finalize_scrubbed },
  Spec.Sha1.digestApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Fn.digest
    verified := .scrubbed Proof.Sha1.RISCV64.digest_scrubbed }]

end VG.Artifacts.Sha1.RISCV64
