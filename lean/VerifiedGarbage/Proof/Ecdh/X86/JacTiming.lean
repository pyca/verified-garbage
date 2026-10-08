import VerifiedGarbage.Impl.Ecdh.X86.WinJac
import VerifiedGarbage.Proof.Ecdh.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! Timing of P-256 ECDH with the secret-scalar Jacobian window method. -/
namespace VG.Proof.Ecdh.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Ecdh.X86

def jacExchange : Prog isa := Cfg.exchangeJacWindow p256
materialize_code jacExchange

theorem jacExchange_ct : ConstantTime isa ecdhX86.pre ecdhX86.pub jacExchange :=
  VG.Taint.constantTime (A:=sseTaint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide_weak VG.Proof.Ecdsa.X86.weak)

end VG.Proof.Ecdh.X86
