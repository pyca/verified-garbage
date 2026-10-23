module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on PPC64LE

The code uses 160 bytes of stack, the frame of `vg_poly1305_blocks`; its
calls (`bl`) keep the return address in the link register, which it saves in
its working space. Each function keeps its working space (648 bytes, `work`)
in a frame of 688 bytes on the stack (`withStackScratchWiped`), zeroed after
the code, as it holds the one-time Poly1305 key and keystream.
`vg_chacha20_poly1305_seal_gather` copies the slices to `dst` and calls
`vg_chacha20_poly1305_seal` on them there, from a frame of 80 bytes that keeps
its arguments and return address, so it uses 80 bytes of stack more.
-/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.PPC64LE

def artifacts : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 688 .r10 81 Impl.ChaCha20Poly1305.PPC64LE.«seal»
    stack := 848
    verified := Proof.ChaCha20Poly1305.PPC64LE.seal_framed },
  Spec.ChaCha20Poly1305.openApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 688 .r10 81 Impl.ChaCha20Poly1305.PPC64LE.«open»
    stack := 848
    verified := Proof.ChaCha20Poly1305.PPC64LE.open_framed },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact PPC64LE.target {
    code := Impl.ChaCha20Poly1305.PPC64LE.SealGather.sealGather
    stack := 928
    verified := Proof.ChaCha20Poly1305.PPC64LE.Gather.sealGather_verified }]

end VG.Artifacts.ChaCha20Poly1305.PPC64LE
