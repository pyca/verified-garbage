module

public import VerifiedGarbage.Impl.Blake2.AArch64.Stream
public import VerifiedGarbage.Proof.Blake2.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.TCB.AArch64.Print

/-! # BLAKE2s (RFC 7693) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.AArch64

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.init Spec.Blake2.s
    verified := .scrubbed Proof.Blake2.AArch64.Fn.initS },
  Spec.Blake2.updateSApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.update Spec.Blake2.s
    verified := .scrubbed Proof.Blake2.AArch64.Fn.updateS },
  Spec.Blake2.finalizeSApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.finalize Spec.Blake2.s
    verified := .scrubbed Proof.Blake2.AArch64.Fn.finalizeS }]

end VG.Artifacts.Blake2s.AArch64
