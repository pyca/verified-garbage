module

public import VerifiedGarbage.Proof.Blake2.X86.Blake2b
public import VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified
import VerifiedGarbage.Proof.Blake2.X86.LitB
public import VerifiedGarbage.Proof.Blake2.X86.Scrub
public import VerifiedGarbage.Impl.Blake2.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # BLAKE2b (RFC 7693) on x86 -/

@[expose] public section

namespace VG.Artifacts.Blake2b.X86

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.init Spec.Blake2.b
    verified := .scrubbed Proof.Blake2.X86.Scrub.initB_scrubbed },
  Spec.Blake2.updateBApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.updateB
    verified := .scrubbed Proof.Blake2.X86.Scrub.updateB_scrubbed },
  Spec.Blake2.finalizeBApi.artifact X86.target {
    code := Impl.Blake2.X86.Fn.finalizeB
    verified := .scrubbed Proof.Blake2.X86.Scrub.finalizeB_scrubbed }]

end VG.Artifacts.Blake2b.X86
