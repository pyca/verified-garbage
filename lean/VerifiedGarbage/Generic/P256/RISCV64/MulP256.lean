module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulLit

/-! # P-256's point multiplication on RISC-V -/

@[expose] public section

namespace VG.Generic.P256.RISCV64.MulP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p256.mulApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.mulP256
    verified := Proof.Ecdsa.RISCV64.P256.mul_verified h.law }]

end VG.Generic.P256.RISCV64.MulP256
