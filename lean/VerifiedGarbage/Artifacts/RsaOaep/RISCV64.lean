module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Inst
public import VerifiedGarbage.Spec.RsaOaep.Tables

/-! # RSAES-OAEP on RISC-V, with both hash functions as tables -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.RISCV64

open VG.Proof.RsaOaep.RISCV64 (OK enc_ok dec_ok)
open VG.Proof.HashTable.RISCV64 (vars tables fnsOf)

def artifacts : List Artifact :=
  if h : OK vars then [
    Spec.RsaOaep.decryptTablesApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decrypt (fnsOf vars)
      stack := 3472
      verified := dec_ok vars h },
    Spec.RsaOaep.encryptTablesApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt (fnsOf vars)
      stack := 336
      verified := enc_ok vars h }]
  else []

end VG.Artifacts.RsaOaep.RISCV64
