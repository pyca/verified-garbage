module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Scrub
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSASSA-PSS (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPss.PPC64LE

open VG.Proof.RsaPss.PPC64LE (OK)
open VG.Proof.MdHashTable.PPC64LE (mvars)

def artifacts : List Artifact :=
  if h : OK mvars mvars then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact PPC64LE.target (Proof.RsaPss.PPC64LE.Scrub.verifyReg h),
    Spec.RsaPss.signPrecomputedMdTableApi.artifact PPC64LE.target (Proof.RsaPss.PPC64LE.Scrub.signReg h)]
  else []

end VG.Artifacts.RsaPss.PPC64LE
