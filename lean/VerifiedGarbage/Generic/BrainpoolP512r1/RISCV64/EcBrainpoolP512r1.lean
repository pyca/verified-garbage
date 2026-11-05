module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhLit

/-! # brainpoolP512r1 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.RISCV64.EcBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.publicKeyBrainpoolP512r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP512r1.pk_verified h.law }]

end VG.Generic.BrainpoolP512r1.RISCV64.EcBrainpoolP512r1
