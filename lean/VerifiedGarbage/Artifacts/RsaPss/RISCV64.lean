module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Fn
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSASSA-PSS (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPss.RISCV64

open VG.Proof.RsaPss.RISCV64 (OK)
open VG.Proof.MdHashTable.RISCV64 (vars tables fnsOf fns3)

def artifacts : List Artifact :=
  if h : OK vars vars then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaPss.RISCV64.Fn.verifyPrecomputed (fnsOf vars) (fns3 vars)
      verified := Proof.RsaPss.RISCV64.Fn.verifyPrecomputed h },
    Spec.RsaPss.signPrecomputedMdTableApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaPss.RISCV64.Fn.signPrecomputed (fnsOf vars) (fns3 vars)
      verified := Proof.RsaPss.RISCV64.Fn.signPrecomputed h }]
  else []

end VG.Artifacts.RsaPss.RISCV64
