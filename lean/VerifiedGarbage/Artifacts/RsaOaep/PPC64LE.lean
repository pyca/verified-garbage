module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Inst
public import VerifiedGarbage.Spec.RsaOaep.Tables
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSAES-OAEP on PPC64LE, with both hash functions as tables -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.PPC64LE

open VG.Proof.RsaOaep.PPC64LE (OK enc_ok dec_ok)
open VG.Proof.HashTable.PPC64LE (vars tables fnsOf)

def artifacts : List Artifact :=
  if h : OK vars then [
    Spec.RsaOaep.decryptTablesApi.artifact PPC64LE.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decrypt (fnsOf vars)
      stack := 3776
      verified := dec_ok vars h },
    Spec.RsaOaep.encryptTablesApi.artifact PPC64LE.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.encrypt (fnsOf vars)
      stack := 304
      verified := enc_ok vars h }]
  else []

end VG.Artifacts.RsaOaep.PPC64LE
