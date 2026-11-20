module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Md5.RISCV64.Scrub
public import VerifiedGarbage.Impl.Md5.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # MD5 (RFC 1321) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Md5.RISCV64

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Fn.init
    verified := .scrubbed Proof.Md5.RISCV64.init_scrubbed },
  Spec.Md5.updateApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Fn.update
    verified := .scrubbed Proof.Md5.RISCV64.update_scrubbed },
  Spec.Md5.finalizeApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Fn.finalize
    verified := .scrubbed Proof.Md5.RISCV64.finalize_scrubbed }]

end VG.Artifacts.Md5.RISCV64
