module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.VerifyLit

/-! # ECDSA over P-256 (FIPS 186-5) on RISC-V -/

@[expose] public section

namespace VG.Generic.P256.RISCV64.EcdsaP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.P256.signApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.Sign.signP256
    consts := Impl.Ecdsa.RISCV64.Comb.p256CombConsts
    verified := Proof.Ecdsa.RISCV64.P256.sign_verified h.law },
  Spec.Ecdsa.P256.verifyApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.Verify.verifyP256
    verified := Proof.Ecdsa.RISCV64.P256.verify_verified h.law }]

end VG.Generic.P256.RISCV64.EcdsaP256
