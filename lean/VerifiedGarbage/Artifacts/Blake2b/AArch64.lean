module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Impl.Blake2.AArch64.Stream
import VerifiedGarbage.Proof.Blake2.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2b (RFC 7693) on AArch64 -/

namespace VG.Artifacts.Blake2b.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Blake2.initBApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.init Spec.Blake2.b
    verified := Proof.Blake2.AArch64.Fn.initB },
  Spec.Blake2.updateBApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.update Spec.Blake2.b
    verified := Proof.Blake2.AArch64.Fn.updateB },
  Spec.Blake2.finalizeBApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.finalize Spec.Blake2.b
    verified := Proof.Blake2.AArch64.Fn.finalizeB }]

spec_apis artifacts

end VG.Artifacts.Blake2b.AArch64
