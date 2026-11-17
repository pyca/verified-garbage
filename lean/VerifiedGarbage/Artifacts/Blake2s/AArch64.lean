module

public import VerifiedGarbage.Proof.Blake2.AArch64.Compress
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Verified
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.CT
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # BLAKE2s (RFC 7693) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.AArch64

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact AArch64.target {
    code := Impl.Residue.AArch64.withClears [.x9] [] none (Impl.Blake2.AArch64.Stream.init Spec.Blake2.s)
    verified := Proof.Blake2.AArch64.Stream.initSCleared_verified
    residue := some ⟨Proof.Blake2.AArch64.Stream.initSCleared_noResidue _⟩ },
  Spec.Blake2.updateSApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 576 .x4 (Impl.Blake2.AArch64.Stream.update Spec.Blake2.s)
    verified := Proof.Blake2.AArch64.Stream.updateS_framed },
  Spec.Blake2.finalizeSApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 576 .x3 (Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.s)
    verified := Proof.Blake2.AArch64.Stream.finalizeS_framed }]

end VG.Artifacts.Blake2s.AArch64
