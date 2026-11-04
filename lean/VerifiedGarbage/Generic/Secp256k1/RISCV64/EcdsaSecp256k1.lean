module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.VerifyLit

/-! # ECDSA over secp256k1 (FIPS 186-5) on RISC-V -/

@[expose] public section

namespace VG.Generic.Secp256k1.RISCV64.EcdsaSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.verifySecp256k1
    consts := Impl.Ecdsa.RISCV64.Comb.secp256k1CombConsts
    verified := Proof.Ecdsa.RISCV64.Secp256k1.verify_verified h.law }]

end VG.Generic.Secp256k1.RISCV64.EcdsaSecp256k1
