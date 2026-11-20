module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.EcdhLit
public import VerifiedGarbage.Proof.BrainpoolP320r1.RISCV64.Law

/-! # ECDH over brainpoolP320r1 (SP 800-56A) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdhBrainpoolP320r1.RISCV64

open VG.Proof.BrainpoolP320r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.exchangeBrainpoolP320r1
    verified := .scrubbed (Proof.Ecdh.RISCV64.BrainpoolP320r1.exchange_scrubbed hasLaw.law) }]

end VG.Artifacts.EcdhBrainpoolP320r1.RISCV64
