module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CMAC (NIST SP 800-38B) on PPC64LE -/

namespace VG.Artifacts.CmacAes.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Cmac.aesInitApi.artifact PPC64LE.target {
    code := Impl.CmacAes.Stream.PPC64LE.Fn.init
    verified := Proof.CmacAes.Stream.PPC64LE.Scrub.init_scrubbed },
  Spec.Cmac.aesAbsorbApi.artifact PPC64LE.target {
    code := Impl.CmacAes.Stream.PPC64LE.Fn.absorb
    verified := Proof.CmacAes.Stream.PPC64LE.Scrub.absorb_scrubbed },
  Spec.Cmac.aesFinishApi.artifact PPC64LE.target {
    code := Impl.CmacAes.Stream.PPC64LE.Fn.finish
    verified := Proof.CmacAes.Stream.PPC64LE.Scrub.finish_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CmacAes.PPC64LE
