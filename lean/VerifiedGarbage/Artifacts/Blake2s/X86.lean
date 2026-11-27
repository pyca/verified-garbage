module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Blake2.X86.Blake2s
import VerifiedGarbage.Proof.Blake2.X86.LitS
import VerifiedGarbage.Proof.Blake2.X86.Scrub
import VerifiedGarbage.Impl.Blake2.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2s (RFC 7693) on x86 -/

namespace VG.Artifacts.Blake2s.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Blake2.initSApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.init Spec.Blake2.s
    verified := Proof.Blake2.X86.Scrub.initS_scrubbed },
  Spec.Blake2.updateSApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.updateS
    verified := Proof.Blake2.X86.Scrub.updateS_scrubbed },
  Spec.Blake2.finalizeSApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.finalizeS
    verified := Proof.Blake2.X86.Scrub.finalizeS_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blake2s.X86
