module

public import VerifiedGarbage.Proof.Rc4.RISCV64.Scrub
public import VerifiedGarbage.Impl.Rc4.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Rc4.RISCV64.Lit

/-! # RC4 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rc4.RISCV64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact RISCV64.target {
    code := Impl.Rc4.RISCV64.Fn.init
    verified := .scrubbed Proof.Rc4.RISCV64.Scrub.init_scrubbed },
  Spec.Rc4.applyApi.artifact RISCV64.target {
    code := Impl.Rc4.RISCV64.Fn.apply
    verified := .scrubbed Proof.Rc4.RISCV64.Scrub.apply_scrubbed }]

end VG.Artifacts.Rc4.RISCV64
