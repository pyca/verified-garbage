module

public import VerifiedGarbage.Proof.Blake2.AArch64.Compress
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2b (RFC 7693) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Blake2b.AArch64

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Stream.init Spec.Blake2.b
    verified := Proof.Blake2.AArch64.Stream.initB_verified },
  Spec.Blake2.updateBApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 576 .x4 (Impl.Blake2.AArch64.Stream.update Spec.Blake2.b)
    stack := 16 + 576
    verified := Proof.Blake2.AArch64.Stream.updateB_framed },
  Spec.Blake2.finalizeBApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 576 .x3 (Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.b)
    stack := 16 + 576
    verified := Proof.Blake2.AArch64.Stream.finalizeB_framed }]

end VG.Artifacts.Blake2b.AArch64
