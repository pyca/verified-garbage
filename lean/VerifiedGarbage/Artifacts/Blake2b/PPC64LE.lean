module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Blake2.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2b (RFC 7693) on PPC64LE -/

namespace VG.Artifacts.Blake2b.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Blake2.initBApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Fn.initB
    verified := Proof.Blake2.PPC64LE.Scrub.initB_scrubbed },
  Spec.Blake2.updateBApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Fn.updateB
    verified := Proof.Blake2.PPC64LE.Scrub.updateB_scrubbed },
  Spec.Blake2.finalizeBApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Fn.finalizeB
    verified := Proof.Blake2.PPC64LE.Scrub.finalizeB_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blake2b.PPC64LE
