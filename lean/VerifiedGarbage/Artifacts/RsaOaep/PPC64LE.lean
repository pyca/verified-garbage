module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaOaep.MdTables
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Scrub
import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-OAEP (RFC 8017) on PPC64LE -/

namespace VG.Artifacts.RsaOaep.PPC64LE

open VG.Proof.MdHashTable.PPC64LE (mvars tables fns3)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact PPC64LE.target {
    tables := [("hash", tables mvars), ("mgf1", tables mvars)]
    code := Impl.RsaOaep.PPC64LE.Fn.decryptP (fns3 mvars)
    verified := Proof.RsaOaep.PPC64LE.Scrub.decryptP_scrubbed },
  Spec.RsaOaep.encryptMdTablesApi.artifact PPC64LE.target {
    tables := [("hash", tables mvars), ("mgf1", tables mvars)]
    code := Impl.RsaOaep.PPC64LE.Fn.encrypt (fns3 mvars)
    verified := Proof.RsaOaep.PPC64LE.Scrub.encrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.RsaOaep.PPC64LE
