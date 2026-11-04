module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Verified
public import VerifiedGarbage.Spec.RsaPss.Table

/-! # RSASSA-PSS on PPC64LE, with the hash functions as tables -/

@[expose] public section

namespace VG.Artifacts.RsaPss.PPC64LE

open VG.Proof.RsaPss.PPC64LE (OK verify_ok' sign_ok')
open VG.Proof.MdHashTable.PPC64LE (mvars)
open VG.Proof.HashTable.PPC64LE (vars)

def artifacts : List Artifact :=
  if h : OK mvars vars then [
    Spec.RsaPss.verifyPrecomputedTableApi.artifact PPC64LE.target {
      tables := [("hash", Proof.MdHashTable.PPC64LE.tables mvars), ("mgf1", Proof.HashTable.PPC64LE.tables vars)]
      code := Impl.RsaPss.PPC64LE.verifyPrecomputed (Proof.MdHashTable.PPC64LE.fnsOf mvars)
        (Proof.HashTable.PPC64LE.fnsOf vars)
      stack := 304
      verified := verify_ok' h },
    Spec.RsaPss.signTableApi.artifact PPC64LE.target {
      tables := [("hash", Proof.MdHashTable.PPC64LE.tables mvars), ("mgf1", Proof.HashTable.PPC64LE.tables vars)]
      code := Impl.RsaPss.PPC64LE.Sign.sign (Proof.MdHashTable.PPC64LE.fnsOf mvars)
        (Proof.HashTable.PPC64LE.fnsOf vars)
      stack := 3776
      verified := sign_ok' h }]
  else []

end VG.Artifacts.RsaPss.PPC64LE
