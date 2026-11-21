module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Scrub
public import VerifiedGarbage.Impl.RsaPss.PPC64LE.Fn
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSASSA-PSS (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPss.PPC64LE

open VG.Proof.MdHashTable.PPC64LE (mvars tables fnsOf fns3)

def artifacts : List Artifact := [
  Spec.RsaPss.verifyPrecomputedMdTableApi.artifact PPC64LE.target {
    tables := [("hash", tables mvars), ("mgf1", tables mvars)]
    code := Impl.RsaPss.PPC64LE.Fn.verifyPrecomputed (fnsOf mvars) (fns3 mvars)
    verified := Proof.RsaPss.PPC64LE.Scrub.verifyPrecomputed_scrubbed },
  Spec.RsaPss.signPrecomputedMdTableApi.artifact PPC64LE.target {
    tables := [("hash", tables mvars), ("mgf1", tables mvars)]
    code := Impl.RsaPss.PPC64LE.Fn.signP (fnsOf mvars) (fns3 mvars)
    verified := Proof.RsaPss.PPC64LE.Scrub.signP_scrubbed }]

end VG.Artifacts.RsaPss.PPC64LE
