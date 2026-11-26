module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Blake2.X86.Blake2b
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified
import VerifiedGarbage.Proof.Blake2.X86.LitB
import VerifiedGarbage.Proof.Blake2.X86.Scrub
import VerifiedGarbage.Impl.Blake2.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2b (RFC 7693) on x86 -/

namespace VG.Artifacts.Blake2b.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Blake2.initBApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.init Spec.Blake2.b
    verified := Proof.Blake2.X86.Scrub.initB_scrubbed },
  Spec.Blake2.updateBApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.updateB
    verified := Proof.Blake2.X86.Scrub.updateB_scrubbed },
  Spec.Blake2.finalizeBApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.finalizeB
    verified := Proof.Blake2.X86.Scrub.finalizeB_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blake2b.X86
