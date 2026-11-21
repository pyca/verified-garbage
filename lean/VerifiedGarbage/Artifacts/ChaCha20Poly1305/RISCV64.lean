module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.RISCV64

def artifacts : List Artifact := [
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

end VG.Artifacts.ChaCha20Poly1305.RISCV64
