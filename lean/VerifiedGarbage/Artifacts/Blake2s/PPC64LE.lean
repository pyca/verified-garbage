module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Blake2.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2s (RFC 7693) on PPC64LE -/

namespace VG.Artifacts.Blake2s.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Blake2.initSApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Fn.initS
    verified := Proof.Blake2.PPC64LE.Scrub.initS_scrubbed },
  Spec.Blake2.updateSApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Fn.updateS
    verified := Proof.Blake2.PPC64LE.Scrub.updateS_scrubbed },
  Spec.Blake2.finalizeSApi.artifact PPC64LE.target {
    code := Impl.Blake2.PPC64LE.Fn.finalizeS
    verified := Proof.Blake2.PPC64LE.Scrub.finalizeS_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blake2s.PPC64LE
