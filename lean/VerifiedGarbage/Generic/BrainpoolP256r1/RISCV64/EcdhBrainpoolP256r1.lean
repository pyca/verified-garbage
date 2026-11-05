module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP256r1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.EcdhLit

/-! # ECDH over brainpoolp256r1 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.RISCV64.EcdhBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdh.BrainpoolP256r1.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhBrainpoolP256r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP256r1.ecdh_verified h.law }]

end VG.Generic.BrainpoolP256r1.RISCV64.EcdhBrainpoolP256r1
