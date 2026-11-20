module

public import VerifiedGarbage.Proof.Poly1305.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Poly1305.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit

/-! # Poly1305 (RFC 8439 §2.5) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Poly1305.RISCV64

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact RISCV64.target {
    code := Impl.Poly1305.RISCV64.Fn.init
    verified := .scrubbed Proof.Poly1305.RISCV64.Scrub.init_scrubbed },
  Spec.Poly1305.updateApi.artifact RISCV64.target {
    code := Impl.Poly1305.RISCV64.Fn.update
    verified := .scrubbed Proof.Poly1305.RISCV64.Scrub.update_scrubbed },
  Spec.Poly1305.finalizeApi.artifact RISCV64.target {
    code := Impl.Poly1305.RISCV64.Fn.finalize
    verified := .scrubbed Proof.Poly1305.RISCV64.Scrub.finalize_scrubbed }]

end VG.Artifacts.Poly1305.RISCV64
