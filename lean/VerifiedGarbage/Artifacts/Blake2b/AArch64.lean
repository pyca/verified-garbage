module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Blake2.AArch64.Compress
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Verified
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.CT
public import VerifiedGarbage.Proof.Blake2.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # BLAKE2b (RFC 7693) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Blake2b.AArch64

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact AArch64.target {
    code := Impl.Residue.AArch64.withClears [.x9] [] none (Impl.Blake2.AArch64.Stream.init Spec.Blake2.b)
    verified := Proof.Blake2.AArch64.Stream.initBCleared_verified
    residue := some ⟨Proof.Blake2.AArch64.Stream.initBCleared_noResidue _⟩ },
  Spec.Blake2.updateBApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.StackScratch.AArch64.withStackScratch 112 .x4 (Impl.Blake2.AArch64.Stream.update Spec.Blake2.b)
    verified := Proof.Blake2.AArch64.Stream.updateB_framed }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [],
       []⟩
    (Proof.Blake2.AArch64.Scrub.updateBOk 128)),
  Spec.Blake2.finalizeBApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.StackScratch.AArch64.withStackScratch 112 .x3 (Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.b)
    verified := Proof.Blake2.AArch64.Stream.finalizeB_framed }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [],
       []⟩
    (Proof.Blake2.AArch64.Scrub.finalizeBOk 128))]

end VG.Artifacts.Blake2b.AArch64
