module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPss.MdTable
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaPss.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PSS (RFC 8017) on RISC-V -/

namespace VG.Artifacts.RsaPss.RISCV64

open VG.Proof.RsaPss.RISCV64 (OK)
open VG.Proof.MdHashTable.RISCV64 (vars tables fnsOf fns3)

public def artifacts : List (Artifact RISCV64.target) :=
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

spec_apis artifacts

end VG.Artifacts.RsaPss.RISCV64
