module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Scrub
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Fn
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSAES-OAEP (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.PPC64LE

open VG.Proof.MdHashTable.PPC64LE (mvars tables fns3)

def artifacts : List Artifact := [
  Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact PPC64LE.target {
    tables := [("hash", tables mvars), ("mgf1", tables mvars)]
    code := Impl.RsaOaep.PPC64LE.Fn.decryptP (fns3 mvars)
    verified := Proof.RsaOaep.PPC64LE.Scrub.decryptP_scrubbed },
  Spec.RsaOaep.encryptMdTablesApi.artifact PPC64LE.target {
    tables := [("hash", tables mvars), ("mgf1", tables mvars)]
    code := Impl.RsaOaep.PPC64LE.Fn.encrypt (fns3 mvars)
    verified := Proof.RsaOaep.PPC64LE.Scrub.encrypt_scrubbed }]

end VG.Artifacts.RsaOaep.PPC64LE
