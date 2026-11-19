module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Scrub
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSAES-OAEP (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.PPC64LE

open VG.Proof.RsaOaep.PPC64LE (OK)
open VG.Proof.MdHashTable.PPC64LE (mvars)

def artifacts : List Artifact :=
  if h : OK mvars then [
    Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact PPC64LE.target
      (Proof.RsaOaep.PPC64LE.Scrub.decryptReg h),
    Spec.RsaOaep.encryptMdTablesApi.artifact PPC64LE.target (Proof.RsaOaep.PPC64LE.Scrub.encryptReg h)]
  else []

end VG.Artifacts.RsaOaep.PPC64LE
