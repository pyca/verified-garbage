module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Impl.Blake2.AArch64.Stream
import VerifiedGarbage.Proof.Blake2.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2s (RFC 7693) on AArch64 -/

namespace VG.Artifacts.Blake2s.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Blake2.initSApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.init Spec.Blake2.s
    verified := Proof.Blake2.AArch64.Fn.initS },
  Spec.Blake2.updateSApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.update Spec.Blake2.s
    verified := Proof.Blake2.AArch64.Fn.updateS },
  Spec.Blake2.finalizeSApi.artifact AArch64.target {
    code := Impl.Blake2.AArch64.Fn.finalize Spec.Blake2.s
    verified := Proof.Blake2.AArch64.Fn.finalizeS }]

spec_apis artifacts

end VG.Artifacts.Blake2s.AArch64
