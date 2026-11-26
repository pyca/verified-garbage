module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.EcdhVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.EcdhLit
import VerifiedGarbage.Proof.BrainpoolP320r1.RISCV64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over brainpoolP320r1 (SP 800-56A) on RISC-V -/

namespace VG.Artifacts.EcdhBrainpoolP320r1.RISCV64

open VG.Proof.BrainpoolP320r1.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.exchangeBrainpoolP320r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP320r1.exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhBrainpoolP320r1.RISCV64
