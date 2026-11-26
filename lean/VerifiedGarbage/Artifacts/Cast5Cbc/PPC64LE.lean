module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cbc
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.PPC64LE.Scrub
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CBC on PPC64LE -/

namespace VG.Artifacts.Cast5Cbc.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Cast5.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.Cast5.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.Cast5.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Cast5.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.Cast5.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Cbc.PPC64LE
