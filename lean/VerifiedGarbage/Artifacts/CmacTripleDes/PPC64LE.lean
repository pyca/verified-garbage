module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Lit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on PPC64LE -/

namespace VG.Artifacts.CmacTripleDes.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Cmac.tdesStreamInitApi.artifact PPC64LE.target {
    code := Impl.CmacTripleDes.Stream.PPC64LE.Fn.init
    verified := Proof.CmacTripleDes.Stream.PPC64LE.Scrub.init_scrubbed },
  Spec.Cmac.tdesAbsorbApi.artifact PPC64LE.target {
    code := Impl.CmacTripleDes.Stream.PPC64LE.Fn.absorb
    verified := Proof.CmacTripleDes.Stream.PPC64LE.Scrub.absorb_scrubbed },
  Spec.Cmac.tdesFinishApi.artifact PPC64LE.target {
    code := Impl.CmacTripleDes.Stream.PPC64LE.Fn.finish
    verified := Proof.CmacTripleDes.Stream.PPC64LE.Scrub.finish_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CmacTripleDes.PPC64LE
