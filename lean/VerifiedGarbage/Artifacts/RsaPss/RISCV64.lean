module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub
public import VerifiedGarbage.Proof.RsaPss.RISCV64.SignP
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSASSA-PSS (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaPss.RISCV64

open VG.Proof.RsaPss.RISCV64 (OK verify_ok signP_ok)
open VG.Proof.MdHashTable.RISCV64 (vars tables fnsOf fns3)

def artifacts : List Artifact :=
  if h : OK vars vars then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaPss.RISCV64.verifyPrecomputed (fnsOf vars)
        (fns3 vars)
      verified := verify_ok h }
      (Proof.Rsa.RISCV64.Scrub.pssVerifyOut _ _ _)),
    Spec.RsaPss.signPrecomputedMdTableApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Impl.RsaPss.RISCV64.Sign.signP (fnsOf vars) (fns3 vars)
      verified := signP_ok h }
      (Proof.Rsa.RISCV64.Scrub.pssSignOut _ _ _))]
  else []

end VG.Artifacts.RsaPss.RISCV64
