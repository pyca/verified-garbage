module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Poly1305.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit

/-! # Poly1305 (RFC 8439 §2.5) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Poly1305.RISCV64

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact RISCV64.target {
    code := Impl.Poly1305.RISCV64.init
    verified := Proof.Poly1305.RISCV64.Shared.init },
  Spec.Poly1305.updateApi.artifact RISCV64.target {
    code := Impl.Poly1305.RISCV64.update
    verified := Proof.Poly1305.RISCV64.Shared.update },
  Spec.Poly1305.finalizeApi.artifact RISCV64.target {
    code := Impl.Poly1305.RISCV64.finalize
    verified := Proof.Poly1305.RISCV64.Shared.finalize }]

end VG.Artifacts.Poly1305.RISCV64
