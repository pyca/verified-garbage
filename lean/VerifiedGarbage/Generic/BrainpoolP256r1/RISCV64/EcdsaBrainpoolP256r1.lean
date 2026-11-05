module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.VerifyLit

/-! # ECDSA over brainpoolp256r1 (FIPS 186-5) on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.RISCV64.EcdsaBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP256r1.inst.curve.len false
      Impl.Ecdsa.RISCV64.verifyBrainpoolP256r1
    consts := Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts
    stack := 80
    verified := Proof.Ecdsa.RISCV64.BrainpoolP256r1.verifyHash_verified h.law }]

end VG.Generic.BrainpoolP256r1.RISCV64.EcdsaBrainpoolP256r1
