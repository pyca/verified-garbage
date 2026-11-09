module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.VerifyLit
public import VerifiedGarbage.Proof.P384.RISCV64.Law

/-! # ECDSA over P-384 (FIPS 186-5) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdsaP384.RISCV64

open VG.Proof.P384.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.RISCV64.VerifyComb.verifyP384
    stack := 80
    verified := Proof.Ecdsa.RISCV64.P384.verifyHash_verified hasLaw.law }]

end VG.Artifacts.EcdsaP384.RISCV64
