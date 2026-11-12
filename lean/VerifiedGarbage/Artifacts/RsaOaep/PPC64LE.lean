module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Inst
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Verified
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSAES-OAEP (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.PPC64LE

open VG.Proof.RsaOaep.PPC64LE (OK enc_ok dec_ok decP_ok)
open VG.Proof.MdHashTable.PPC64LE (mvars tables fns3)

def artifacts : List Artifact :=
  if h : OK mvars then [
    Spec.RsaOaep.decryptMdTablesApi.artifact PPC64LE.target {
      tables := [("hash", tables mvars), ("mgf1", tables mvars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decrypt (fns3 mvars)
      stack := 3792
      verified := dec_ok mvars h },
    Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact PPC64LE.target {
      tables := [("hash", tables mvars), ("mgf1", tables mvars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decryptP (fns3 mvars)
      stack := 3792
      verified := decP_ok mvars h },
    Spec.RsaOaep.encryptMdTablesApi.artifact PPC64LE.target {
      tables := [("hash", tables mvars), ("mgf1", tables mvars)]
      code := Impl.RsaOaep.PPC64LE.encrypt (fns3 mvars)
      stack := 304
      verified := enc_ok mvars h }]
  else []

end VG.Artifacts.RsaOaep.PPC64LE
