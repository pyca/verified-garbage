module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPss.MdTable
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Scrub
import VerifiedGarbage.Impl.RsaPss.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PSS (RFC 8017) on PPC64LE -/

namespace VG.Artifacts.RsaPss.PPC64LE

open VG.Proof.MdHashTable.PPC64LE (mvars tables fnsOf fns3)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.RsaPss.verifyPrecomputedMdTableApi.artifact PPC64LE.target {
    tables := [("hash", tables mvars), ("mgf1", tables mvars)]
    code := Impl.RsaPss.PPC64LE.Fn.verifyPrecomputed (fnsOf mvars) (fns3 mvars)
    verified := Proof.RsaPss.PPC64LE.Scrub.verifyPrecomputed_scrubbed },
  Spec.RsaPss.signPrecomputedMdTableApi.artifact PPC64LE.target {
    tables := [("hash", tables mvars), ("mgf1", tables mvars)]
    code := Impl.RsaPss.PPC64LE.Fn.signP (fnsOf mvars) (fns3 mvars)
    verified := Proof.RsaPss.PPC64LE.Scrub.signP_scrubbed }]

spec_apis artifacts

end VG.Artifacts.RsaPss.PPC64LE
