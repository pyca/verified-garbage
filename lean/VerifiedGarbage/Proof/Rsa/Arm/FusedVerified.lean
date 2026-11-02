module

public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.RvVerified
import VerifiedGarbage.Proof.Rsa.Arm.RvFusedRest

/-! Fused ARMv7 recovery is verified against the unchanged public contract,
including invalid keys, memory safety, the ABI and constant-time leakage. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm

theorem recover_primes_fused_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] :
    Verified target VG.Impl.Rsa.Arm.RecoverFused.code (Spec.Rsa.recoverPrimesContract abi 56) :=
  recover_primesWith_verified VG.Impl.Rsa.Arm.RecoverFused.body fused_body_vp

end VG.Proof.Rsa.Arm.Recover
