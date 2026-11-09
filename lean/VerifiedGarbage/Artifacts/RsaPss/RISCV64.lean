module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sat
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSASSA-PSS (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPss.RISCV64

open VG.Proof.RsaPss.RISCV64 (OK verify_ok sign_ok)
open VG.Proof.MdHashTable.RISCV64 (vars tables fnsOf fns3)

def artifacts : List Artifact :=
  if h : OK vars vars then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaPss.RISCV64.verifyPrecomputed (fnsOf vars)
        (fns3 vars)
      stack := 336
      verified := verify_ok h },
    Spec.RsaPss.signMdTableApi.artifact RISCV64.target {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaPss.RISCV64.Sign.sign (fnsOf vars) (fns3 vars)
      stack := 3472
      verified := sign_ok h }]
  else []

end VG.Artifacts.RsaPss.RISCV64
