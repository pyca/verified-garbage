module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Verified
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ChaCha20-Poly1305 (RFC 8439 §2.8) on PPC64LE -/

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
