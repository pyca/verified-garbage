module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhLit
public import VerifiedGarbage.Proof.BrainpoolP512r1.RISCV64.Law

/-! # ECDH over brainpoolP512r1 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdhBrainpoolP512r1.RISCV64

open VG.Proof.BrainpoolP512r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.BrainpoolP512r1.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhBrainpoolP512r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP512r1.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhBrainpoolP512r1.RISCV64
