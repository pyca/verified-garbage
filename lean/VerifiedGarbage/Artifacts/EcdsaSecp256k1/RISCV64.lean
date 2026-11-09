module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.VerifyLit
public import VerifiedGarbage.Proof.Secp256k1.RISCV64.Law

/-! # ECDSA over secp256k1 (FIPS 186-5) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdsaSecp256k1.RISCV64

open VG.Proof.Secp256k1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
      Impl.Ecdsa.RISCV64.verifySecp256k1
    stack := 80
    verified := Proof.Ecdsa.RISCV64.Secp256k1.verifyHash_verified hasLaw.law }]

end VG.Artifacts.EcdsaSecp256k1.RISCV64
