module

public import VerifiedGarbage.Proof.Rc4.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.RISCV64.Lit

/-! # Raw RC4 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rc4.RISCV64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact RISCV64.target {
    code := Impl.Rc4.RISCV64.init
    stack := 256
    verified := Proof.Rc4.RISCV64.init_verified },
  Spec.Rc4.applyApi.artifact RISCV64.target {
    code := Impl.Rc4.RISCV64.apply
    stack := 256
    verified := Proof.Rc4.RISCV64.apply_verified }]

end VG.Artifacts.Rc4.RISCV64
