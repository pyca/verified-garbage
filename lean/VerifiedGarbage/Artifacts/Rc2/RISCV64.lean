module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Scrub
public import VerifiedGarbage.Impl.Rc2.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit

/-! # RC2 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rc2.RISCV64

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.Fn.cbcInit
    verified := Proof.Rc2.RISCV64.Scrub.cbcInit_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Rc2.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Rc2.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Rc2.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.Rc2.RISCV64
