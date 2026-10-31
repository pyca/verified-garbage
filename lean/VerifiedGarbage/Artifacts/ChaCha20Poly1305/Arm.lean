module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on ARMv7 -/

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
