module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP256r1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.EcdhLit
public import VerifiedGarbage.Proof.BrainpoolP256r1.RISCV64.Law
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # ECDH over brainpoolP256r1 (SP 800-56A) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdhBrainpoolP256r1.RISCV64

open VG.Proof.BrainpoolP256r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.BrainpoolP256r1.exchangeApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Ecdh.RISCV64.ecdhBrainpoolP256r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP256r1.ecdh_verified hasLaw.law }
    (Proof.EcKey.RISCV64.Scrub.exchangeOut _ _ []))]

end VG.Artifacts.EcdhBrainpoolP256r1.RISCV64
