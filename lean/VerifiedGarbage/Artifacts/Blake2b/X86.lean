module

public import VerifiedGarbage.Proof.Blake2.X86.Blake2b
public import VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified
import VerifiedGarbage.Proof.Blake2.X86.LitB
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2b (RFC 7693) on x86 -/

@[expose] public section

namespace VG.Artifacts.Blake2b.X86

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact X86.target {
    code := Impl.Blake2.X86.Stream.init Spec.Blake2.b
    verified := Proof.Blake2.X86.B.initB_verified },
  Spec.Blake2.updateBApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 604 5 (Impl.Blake2.X86.Stream.update 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress)
    stack := 32 + 604
    verified := Proof.Blake2.X86.B.updateB_framed },
  Spec.Blake2.finalizeBApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 600 4 (Impl.Blake2.X86.Stream.finalize 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress)
    stack := 32 + 600
    verified := Proof.Blake2.X86.B.finalizeB_framed }]

end VG.Artifacts.Blake2b.X86
