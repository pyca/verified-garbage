module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on RISC-V -/

namespace VG.Artifacts.ChaCha20Poly1305.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.ChaCha20Poly1305.sealApi.artifact RISCV64.target {
    code := Impl.ChaCha20Poly1305.RISCV64.Fn.«seal»
    verified := Proof.ChaCha20Poly1305.RISCV64.Scrub.seal_scrubbed },
  Spec.ChaCha20Poly1305.openZeroApi.artifact RISCV64.target {
    code := Impl.ChaCha20Poly1305.RISCV64.Fn.«open»
    verified := Proof.ChaCha20Poly1305.RISCV64.Scrub.open_scrubbed },
  Spec.ChaCha20Poly1305.openToApi.artifact RISCV64.target {
    code := Impl.ChaCha20Poly1305.RISCV64.Fn.openTo
    verified := Proof.ChaCha20Poly1305.RISCV64.Scrub.openTo_scrubbed },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact RISCV64.target {
    code := Impl.ChaCha20Poly1305.RISCV64.Fn.sealGather
    verified := Proof.ChaCha20Poly1305.RISCV64.Scrub.sealGather_scrubbed }]

spec_apis artifacts

end VG.Artifacts.ChaCha20Poly1305.RISCV64
