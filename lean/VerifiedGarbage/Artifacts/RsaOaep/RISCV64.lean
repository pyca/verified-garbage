module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaOaep.MdTables
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-OAEP (RFC 8017) on RISC-V -/

namespace VG.Artifacts.RsaOaep.RISCV64

open VG.Proof.RsaOaep.RISCV64 (OK)
open VG.Proof.MdHashTable.RISCV64 (vars tables fns3)

public def artifacts : List (Artifact RISCV64.target) :=
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

spec_apis artifacts

end VG.Artifacts.RsaOaep.RISCV64
