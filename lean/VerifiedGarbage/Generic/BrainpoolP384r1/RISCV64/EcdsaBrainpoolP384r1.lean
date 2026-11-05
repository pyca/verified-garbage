module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.VerifyLit

/-! # ECDSA over brainpoolp384r1 (FIPS 186-5) on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.RISCV64.EcdsaBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false
      Impl.Ecdsa.RISCV64.verifyBrainpoolP384r1
    stack := 80
    verified := Proof.Ecdsa.RISCV64.BrainpoolP384r1.verifyHash_verified h.law }]

end VG.Generic.BrainpoolP384r1.RISCV64.EcdsaBrainpoolP384r1
