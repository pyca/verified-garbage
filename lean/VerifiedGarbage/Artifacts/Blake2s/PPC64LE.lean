module

public import VerifiedGarbage.Proof.Blake2.PPC64LE.Compress
public import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2s (RFC 7693) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Blake2s.PPC64LE

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Stream.init Spec.Blake2.s
    verified := Proof.Blake2.PPC64LE.Stream.initS_verified },
  Spec.Blake2.updateSApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 608 .r7 (Impl.Blake2.PPC64LE.Stream.update Spec.Blake2.s)
    stack := 48 + 608
    verified := Proof.Blake2.PPC64LE.Stream.updateS_framed },
  Spec.Blake2.finalizeSApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 608 .r6 (Impl.Blake2.PPC64LE.Stream.finalize Spec.Blake2.s)
    stack := 48 + 608
    verified := Proof.Blake2.PPC64LE.Stream.finalizeS_framed }]

end VG.Artifacts.Blake2s.PPC64LE
