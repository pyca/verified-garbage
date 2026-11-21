module

public import VerifiedGarbage.Impl.Blake2.AArch64.Stream
public import VerifiedGarbage.Proof.Blake2.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.TCB.AArch64.Print

/-! # BLAKE2b (RFC 7693) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Blake2b.AArch64

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.init Spec.Blake2.b
    verified := Proof.Blake2.AArch64.Fn.initB },
  Spec.Blake2.updateBApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.update Spec.Blake2.b
    verified := Proof.Blake2.AArch64.Fn.updateB },
  Spec.Blake2.finalizeBApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.finalize Spec.Blake2.b
    verified := Proof.Blake2.AArch64.Fn.finalizeB }]

end VG.Artifacts.Blake2b.AArch64
