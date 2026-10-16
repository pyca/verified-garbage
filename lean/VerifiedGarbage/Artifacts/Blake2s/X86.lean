module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Blake2.X86.Blake2s
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Sha512.Word64
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2s (RFC 7693) on x86 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.X86

def artifacts : List Artifact := [
  Spec.Blake2.compressSApi.artifact X86.target {
    code := Impl.Blake2.X86.CompressS.compress
    verified := Proof.Blake2.X86.S.compress_verified },
  Spec.Blake2.initSApi.artifact X86.target {
    code := Impl.Blake2.X86.Stream.init Spec.Blake2.s
    verified := Proof.Blake2.X86.S.init_verified },
  Spec.Blake2.updateSApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 604 5 (Impl.Blake2.X86.Stream.update 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress)
    stack := 32 + 604
    verified := Proof.Blake2.X86.S.update_framed },
  Spec.Blake2.finalizeSApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 600 4 (Impl.Blake2.X86.Stream.finalize 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress)
    stack := 32 + 600
    verified := Proof.Blake2.X86.S.finalize_framed },
  Spec.Blake2.updateSScratchApi.artifact X86.target {
    code := Impl.Blake2.X86.Stream.update 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress
    stack := 32
    verified := Proof.Blake2.X86.S.update_verified },
  Spec.Blake2.finalizeSScratchApi.artifact X86.target {
    code := Impl.Blake2.X86.Stream.finalize 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress
    stack := 32
    verified := Proof.Blake2.X86.S.finalize_verified }]

end VG.Artifacts.Blake2s.X86
