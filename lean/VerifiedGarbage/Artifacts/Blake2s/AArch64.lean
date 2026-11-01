module

public import VerifiedGarbage.Proof.Blake2.AArch64.Compress
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2s (RFC 7693) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.AArch64

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Stream.init Spec.Blake2.s
    verified := Proof.Blake2.AArch64.Stream.initS_verified },
  Spec.Blake2.updateSApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 576 .x4 (Impl.Blake2.AArch64.Stream.update Spec.Blake2.s)
    stack := 16 + 576
    verified := Proof.Blake2.AArch64.Stream.updateS_framed },
  Spec.Blake2.finalizeSApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 576 .x3 (Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.s)
    stack := 16 + 576
    verified := Proof.Blake2.AArch64.Stream.finalizeS_framed }]

end VG.Artifacts.Blake2s.AArch64
