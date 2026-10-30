module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHints
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec

@[expose] public section

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
  refine WP.seq (WP.seq (WP.mono (positivePairedChallenge_ok hp h16 roots h h1) fun a ha=>?_))
  refine WP.seq (WP.mono (positivePairedChecksInit_ok hp hc ha.2 ha.1) fun b hb=>?_)
  refine WP.mono (optimizedZ_paired_vector_ok hp hb.2 hb.1) fun c hz=>?_
  refine ifOkElse_ok (fun hzpass=>?_) fun hzfail=>?_
  · refine WP.seq (WP.mono (optimizedR0_paired_vector_ok hp hz.2 (positiveIR_of_IZ hz.1)) fun d hr=>?_)
    refine ifOkElse_ok (fun hrpass=>?_) fun hrfail=>?_
    · refine WP.seq (WP.mono (optimizedHint_paired_vector_ok hp hr.2 (positiveIH_of_IR hr.1)) fun e he=>?_)
      refine WP.seq (WP.mono (WP.pairedRoots (positiveOnesOk_ok hc he.1) he.2 (Nat.zero_le _) hS) fun f hf=>?_)
      exact WP.pairedRoots (positiveKBranch_ok hp hc hf.1) hf.2 (Nat.zero_le _) hS
    · have flag : d.gpr .x24=0 := by
        rw [hr.1.2]; exact bit_zero.mpr (fun h=>(bit_ne.mpr h) (by rw [←hr.1.2]; exact hrfail))
      have fail : ¬ PassV p σ (p.ℓ*t) := by
        intro hpass
        exact (bit_ne.mpr (show ZOk p σ (p.ℓ*t) ∧ R0Ok p σ (p.ℓ*t) from ⟨hpass.1,hpass.2.1⟩))
          (by rw [←hr.1.2]; exact hrfail)
      exact WP.mono (WP.pairedRoots (positiveReject_ok hp hc hr.1.1.b.l hr.1.1.b.sampled fail flag)
        hr.2 (Nat.zero_le _) hS) fun _ hu=>⟨.inr hu.1,hu.2⟩
  · have flag : c.gpr .x24=0 := by
      rw [hz.1.2]; exact bit_zero.mpr (fun h=>(bit_ne.mpr h) (by rw [←hz.1.2]; exact hzfail))
    have fail : ¬ PassV p σ (p.ℓ*t) := by
      intro hpass
      exact (bit_ne.mpr hpass.1) (by rw [←hz.1.2]; exact hzfail)
    exact WP.mono (WP.pairedRoots (positiveReject_ok hp hc hz.1.1.b.l hz.1.1.b.sampled fail flag)
      hz.2 (Nat.zero_le _) hS) fun _ hu=>⟨.inr hu.1,hu.2⟩

end VG.Proof.MlDsa.AArch64.Sign
