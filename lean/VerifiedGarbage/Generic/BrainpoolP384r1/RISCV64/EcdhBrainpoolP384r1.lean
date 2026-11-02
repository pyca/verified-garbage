module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.EcdhLit

/-! # ECDH over brainpoolP384r1 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.RISCV64.EcdhBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdh.BrainpoolP384r1.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhBrainpoolP384r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP384r1.ecdh_verified h.law }]

end VG.Generic.BrainpoolP384r1.RISCV64.EcdhBrainpoolP384r1
