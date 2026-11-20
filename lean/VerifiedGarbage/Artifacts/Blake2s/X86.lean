module

public import VerifiedGarbage.Proof.Blake2.X86.Blake2s
import VerifiedGarbage.Proof.Blake2.X86.LitS
public import VerifiedGarbage.Proof.Blake2.X86.Scrub
public import VerifiedGarbage.Impl.Blake2.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # BLAKE2s (RFC 7693) on x86 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.X86

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.init Spec.Blake2.s
    verified := .scrubbed Proof.Blake2.X86.Scrub.initS_scrubbed },
  Spec.Blake2.updateSApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.updateS
    verified := .scrubbed Proof.Blake2.X86.Scrub.updateS_scrubbed },
  Spec.Blake2.finalizeSApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.finalizeS
    verified := .scrubbed Proof.Blake2.X86.Scrub.finalizeS_scrubbed }]

end VG.Artifacts.Blake2s.X86
