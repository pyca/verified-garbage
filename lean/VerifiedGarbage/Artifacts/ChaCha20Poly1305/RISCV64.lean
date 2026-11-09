module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.RISCV64

def artifacts : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78
      (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»)
    stack := 624
    verified := Proof.ChaCha20Poly1305.RISCV64.seal_framed },
  Spec.ChaCha20Poly1305.openZeroApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78
      (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»)
    stack := 624
    verified := Proof.ChaCha20Poly1305.RISCV64.open_framed },
  Spec.ChaCha20Poly1305.openToApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgsWiped 640 1 78 Impl.ChaCha20Poly1305.RISCV64.openTo
    stack := 640
    verified := Proof.ChaCha20Poly1305.RISCV64.openTo_framed },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact RISCV64.target {
    code := Impl.ChaCha20Poly1305.RISCV64.SealGather.sealGather
    stack := 640
    verified := Proof.ChaCha20Poly1305.RISCV64.Gather.sealGather_verified }]

end VG.Artifacts.ChaCha20Poly1305.RISCV64
