module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# ChaCha20-Poly1305 (RFC 8439 §2.8) on ARMv7

The code uses 8 bytes of stack: it pushes the two stack arguments of
`vg_poly1305_finalize_scratch` around its call; its calls (`bl`) keep the
return address in `lr`, which it saves in its working space. Each function
keeps its working space (632 bytes, `work`) in a frame of 656 bytes on the
stack (`withStackScratchWiped`, which also copies the three other stack
arguments), zeroed after the code, as it holds the one-time Poly1305 key and
keystream. `seal_gather` gathers its slices to its output and calls `seal`
on them there.
-/

@[expose] public section

namespace VG.Artifacts.ChaCha20Poly1305.Arm

def artifacts : List Artifact := [
  Spec.ChaCha20Poly1305.sealApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 Impl.ChaCha20Poly1305.Arm.«seal»
    stack := 664
    verified := Proof.ChaCha20Poly1305.Arm.seal_framed },
  Spec.ChaCha20Poly1305.openApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 Impl.ChaCha20Poly1305.Arm.«open»
    stack := 664
    verified := Proof.ChaCha20Poly1305.Arm.open_framed },
  Spec.ChaCha20Poly1305.sealGatherApi.artifact Arm.target {
    code := Impl.ChaCha20Poly1305.Arm.SealGather.sealGather Proof.ChaCha20Poly1305.Arm.Gather.sealFn.name
      Proof.ChaCha20Poly1305.Arm.Gather.sealFn.code
    stack := 696
    verified := Proof.ChaCha20Poly1305.Arm.Gather.sealGather_verified Proof.ChaCha20Poly1305.Arm.Gather.sealFn }]

end VG.Artifacts.ChaCha20Poly1305.Arm
