module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sat
public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSASSA-PSS on RISC-V, with both hash functions as tables -/

@[expose] public section

namespace VG.Artifacts.RsaPss.RISCV64

open VG.Proof.RsaPss.RISCV64 (OK verify_ok sign_ok)
open VG.Proof.MdHashTable.RISCV64 (vars tables fnsOf)

def artifacts : List Artifact :=
  if h : OK vars Proof.HashTable.RISCV64.vars then [
    Spec.RsaPss.verifyPrecomputedTableApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", Proof.HashTable.RISCV64.tables Proof.HashTable.RISCV64.vars)]
      code := Impl.RsaPss.RISCV64.verifyPrecomputed (fnsOf vars)
        (Proof.HashTable.RISCV64.fnsOf Proof.HashTable.RISCV64.vars)
      stack := 336
      verified := verify_ok h },
    Spec.RsaPss.signTableApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", Proof.HashTable.RISCV64.tables Proof.HashTable.RISCV64.vars)]
      code := Impl.RsaPss.RISCV64.Sign.sign (fnsOf vars) (Proof.HashTable.RISCV64.fnsOf Proof.HashTable.RISCV64.vars)
      stack := 3472
      verified := sign_ok h }]
  else []

end VG.Artifacts.RsaPss.RISCV64
