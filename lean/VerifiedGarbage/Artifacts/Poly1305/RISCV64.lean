module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Poly1305.RISCV64.Scrub
import VerifiedGarbage.Impl.Poly1305.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Poly1305 (RFC 8439 §2.5) on RISC-V -/

namespace VG.Artifacts.Poly1305.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Poly1305.initApi.artifact RISCV64.target {
    code := Impl.Poly1305.RISCV64.Fn.init
    verified := Proof.Poly1305.RISCV64.Scrub.init_scrubbed },
  Spec.Poly1305.updateApi.artifact RISCV64.target {
    code := Impl.Poly1305.RISCV64.Fn.update
    verified := Proof.Poly1305.RISCV64.Scrub.update_scrubbed },
  Spec.Poly1305.finalizeApi.artifact RISCV64.target {
    code := Impl.Poly1305.RISCV64.Fn.finalize
    verified := Proof.Poly1305.RISCV64.Scrub.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Poly1305.RISCV64
