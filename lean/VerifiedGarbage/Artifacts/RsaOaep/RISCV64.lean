module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Inst
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSAES-OAEP (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.RISCV64

open VG.Proof.RsaOaep.RISCV64 (OK enc_ok decP_ok)
open VG.Proof.MdHashTable.RISCV64 (vars tables fns3)

def artifacts : List Artifact :=
  if h : OK vars then [
    Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decryptP (fns3 vars)
      stack := 3488
      verified := decP_ok vars h },
    Spec.RsaOaep.encryptMdTablesApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt (fns3 vars)
      stack := 336
      verified := enc_ok vars h }]
  else []

end VG.Artifacts.RsaOaep.RISCV64
