import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedChecks
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintState

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- A sampled challenge runs every z and r0 check before entering the hint phase. -/
theorem positiveChecksPrefix_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (h : PositiveIB p S σ t s)
    (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.checksPrefix p) s
      (PositiveIH p S σ t 0) := by
  refine WP.seq (WP.mono (positiveChallengeZ_ok hp hc h h1) fun u hu=>?_)
  exact WP.mono (optimizedR0_vector_ok hp (positiveIR_of_IZ hu)) fun v hv=>positiveIH_of_IR hv

end VG.Proof.MlDsa.AArch64.Sign
