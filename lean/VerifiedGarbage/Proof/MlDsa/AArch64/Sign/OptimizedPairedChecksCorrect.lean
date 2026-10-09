import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHints
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem positivePairedChecks_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (h16 : 16≤S) (hS : S<2^64)
    (roots : PairedRoots S s) (h : PositiveIB p S σ t s)
    (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) s fun u=>
      (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks
  refine WP.seq (WP.mono (positivePairedChecksPrefix_ok hp hc h16 roots h h1) fun u hu=>?_)
  refine WP.seq (WP.mono (optimizedHint_paired_vector_ok hp hu.2 hu.1) fun v hv=>?_)
  refine WP.seq (WP.mono (WP.pairedRoots (positiveOnesOk_ok hc hv.1) hv.2 (Nat.zero_le _) hS) fun w hw=>?_)
  exact WP.pairedRoots (positiveKBranch_ok hp hc hw.1) hw.2 (Nat.zero_le _) hS

end VG.Proof.MlDsa.AArch64.Sign
