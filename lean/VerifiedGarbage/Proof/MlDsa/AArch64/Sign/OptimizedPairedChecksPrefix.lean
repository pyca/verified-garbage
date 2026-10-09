import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedR0Timing
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksPrefixTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem positivePairedChallenge_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h16 : 16≤S) (roots : PairedRoots S s)
    (h : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (callAt "vg_mldsa_ntt_positive" Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      (positiveNttArgs cP)) s fun u=>PositiveChallenge p S σ t u ∧ PairedRoots S u := by
  apply WP.pairedRoots (positiveChallenge_ok hp h h1) roots _ h.c.masks.l.st.lay.s64
  exact le_trans (by decide +kernel) h16

theorem positivePairedChecksInit_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : PairedRoots S s)
    (h : PositiveChallenge p S σ t s) :
    WP isa (.block kInit) s fun u=>PositiveIZ p S σ t 0 u ∧ PairedRoots S u := by
  apply WP.pairedRoots (positiveChecksInit_ok hp hc h) roots _ h.c.masks.l.st.lay.s64
  change 0≤S
  exact Nat.zero_le _

theorem positivePairedChecksPrefix_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (h16 : 16≤S) (roots : PairedRoots S s)
    (h : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecksPrefix p) s fun u=>
      PositiveIH p S σ t 0 u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecksPrefix
  refine WP.seq (WP.seq (WP.mono (positivePairedChallenge_ok hp h16 roots h h1) fun a ha=>?_))
  refine WP.seq (WP.mono (positivePairedChecksInit_ok hp hc ha.2 ha.1) fun b hb=>?_)
  refine WP.mono (optimizedZ_paired_vector_ok hp hb.2 hb.1) fun c hc=>?_
  exact WP.mono (optimizedR0_paired_vector_ok hp hc.2 (positiveIR_of_IZ hc.1)) fun d hd=>
    ⟨positiveIH_of_IR hd.1,hd.2⟩

end VG.Proof.MlDsa.AArch64.Sign
