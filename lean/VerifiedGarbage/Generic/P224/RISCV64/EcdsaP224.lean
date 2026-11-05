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

/-! # ECDSA verification over P-224 (FIPS 186-5 §6.4.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.P224.RISCV64.EcdsaP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.P224.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
      Impl.Ecdsa.RISCV64.P224.verifyP224
    consts := Impl.Ecdsa.RISCV64.Comb.p224CombConsts
    stack := 80
    verified := Proof.Ecdsa.RISCV64.P224.verifyHash_verified h.law }]

end VG.Generic.P224.RISCV64.EcdsaP224
