module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on RISC-V

The code calls the verified ChaCha20 and Poly1305 functions, which use no
stack, and keeps our caller's registers it uses across the calls, and our
return address, in its working space. Each function keeps its working space
(616 bytes, `work`) in a frame of 624 bytes on the stack
(`withStackScratchWiped`), zeroed after the code, as it holds the one-time
Poly1305 key and keystream. `vg_chacha20_poly1305_seal_gather` copies the
slices to `dst` and calls `vg_chacha20_poly1305_seal` on them there, from a
frame of 16 bytes that keeps its return address, so it uses 16 bytes of
stack more.
-/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.RISCV64

def artifacts : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 77 Impl.ChaCha20Poly1305.RISCV64.«seal»
    stack := 624
    verified := Proof.ChaCha20Poly1305.RISCV64.seal_framed },
  Spec.ChaCha20Poly1305.openApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 77 Impl.ChaCha20Poly1305.RISCV64.«open»
    stack := 624
    verified := Proof.ChaCha20Poly1305.RISCV64.open_framed },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact RISCV64.target {
    code := Impl.ChaCha20Poly1305.RISCV64.SealGather.sealGather
    stack := 640
    verified := Proof.ChaCha20Poly1305.RISCV64.Gather.sealGather_verified }]

end VG.Artifacts.ChaCha20Poly1305.RISCV64
