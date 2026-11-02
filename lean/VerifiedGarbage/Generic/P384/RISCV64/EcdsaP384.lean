module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.VerifyLit

/-! # ECDSA over P-384 (FIPS 186-5) on RISC-V -/

@[expose] public section

namespace VG.Generic.P384.RISCV64.EcdsaP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.P384.verifyApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.Verify.verifyP384
    verified := Proof.Ecdsa.RISCV64.P384.verify_verified h.law }]

end VG.Generic.P384.RISCV64.EcdsaP384
