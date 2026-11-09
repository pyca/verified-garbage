module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P521
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.VerifyLit
public import VerifiedGarbage.Proof.P521.RISCV64.Law

/-! # ECDSA verification over P-521 (FIPS 186-5 §6.4.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdsaP521.RISCV64

open VG.Proof.P521.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P521.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.RISCV64.P521.verifyP521
    stack := 80
    verified := Proof.Ecdsa.RISCV64.P521.verifyHash_verified hasLaw.law }]

end VG.Artifacts.EcdsaP521.RISCV64
