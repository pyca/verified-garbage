module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhLit
import VerifiedGarbage.Proof.BrainpoolP512r1.RISCV64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over brainpoolP512r1 (SP 800-56A) on RISC-V -/

namespace VG.Artifacts.EcdhBrainpoolP512r1.RISCV64

open VG.Proof.BrainpoolP512r1.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdh.BrainpoolP512r1.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.exchangeBrainpoolP512r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP512r1.exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhBrainpoolP512r1.RISCV64
