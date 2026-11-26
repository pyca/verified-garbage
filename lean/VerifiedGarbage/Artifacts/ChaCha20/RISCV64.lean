module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ChaCha20 (RFC 8439) on RISC-V -/

namespace VG.Artifacts.ChaCha20.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.ChaCha20.initApi.artifact RISCV64.target {
    code := Impl.ChaCha20.RISCV64.Fn.init
    verified := Proof.ChaCha20.RISCV64.Scrub.init_scrubbed },
  Spec.ChaCha20.setNonceApi.artifact RISCV64.target {
    code := Impl.ChaCha20.RISCV64.Fn.setNonce
    verified := Proof.ChaCha20.RISCV64.Scrub.setNonce_scrubbed },
  Spec.ChaCha20.applyApi.artifact RISCV64.target {
    code := Impl.ChaCha20.RISCV64.Fn.apply
    verified := Proof.ChaCha20.RISCV64.Scrub.apply_scrubbed }]

spec_apis artifacts

end VG.Artifacts.ChaCha20.RISCV64
