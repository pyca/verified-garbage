module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.VerifyLit
public import VerifiedGarbage.Proof.P224.RISCV64.Law

/-! # ECDSA verification over P-224 (FIPS 186-5 §6.4.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdsaP224.RISCV64

open VG.Proof.P224.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P224.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
      Impl.Ecdsa.RISCV64.P224.verifyP224
    stack := 80
    verified := Proof.Ecdsa.RISCV64.P224.verifyHash_verified hasLaw.law }]

end VG.Artifacts.EcdsaP224.RISCV64
