module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P192
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.VerifyLit

/-! # ECDSA verification over P-192 (FIPS 186-5 §6.4.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.P192.RISCV64.EcdsaP192

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.Ecdsa.P192.verifyApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.P192.verifyP192
    verified := Proof.Ecdsa.RISCV64.P192.verify_verified h.law }]

end VG.Generic.P192.RISCV64.EcdsaP192
