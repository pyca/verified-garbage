module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhLit

/-! # ECDH over brainpoolP512r1 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.RISCV64.EcdhBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdh.BrainpoolP512r1.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhBrainpoolP512r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP512r1.ecdh_verified h.law }]

end VG.Generic.BrainpoolP512r1.RISCV64.EcdhBrainpoolP512r1
