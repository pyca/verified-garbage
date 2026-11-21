module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Fn
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSAES-OAEP (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.RISCV64

open VG.Proof.RsaOaep.RISCV64 (OK)
open VG.Proof.MdHashTable.RISCV64 (vars tables fns3)

def artifacts : List Artifact :=
  if h : OK vars then [
    Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Fn.decryptPrecomputed (fns3 vars)
      verified := Proof.RsaOaep.RISCV64.Fn.decryptPrecomputed h },
    Spec.RsaOaep.encryptMdTablesApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Fn.encryptPrecomputed (fns3 vars)
      verified := Proof.RsaOaep.RISCV64.Fn.encryptPrecomputed h }]
  else []

end VG.Artifacts.RsaOaep.RISCV64
