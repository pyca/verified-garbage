module

public import VerifiedGarbage.Proof.Blake2.PPC64LE.Compress
public import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2b (RFC 7693) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Blake2b.PPC64LE

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Stream.init Spec.Blake2.b
    verified := Proof.Blake2.PPC64LE.Stream.initB_verified },
  Spec.Blake2.updateBApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 608 .r7 (Impl.Blake2.PPC64LE.Stream.update Spec.Blake2.b)
    stack := 48 + 608
    verified := Proof.Blake2.PPC64LE.Stream.updateB_framed },
  Spec.Blake2.finalizeBApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 608 .r6 (Impl.Blake2.PPC64LE.Stream.finalize Spec.Blake2.b)
    stack := 48 + 608
    verified := Proof.Blake2.PPC64LE.Stream.finalizeB_framed }]

end VG.Artifacts.Blake2b.PPC64LE
