import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksBoundary
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksZVector
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksLowVector
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksHints

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached odd mask is retained through every response and hint check.
The frame comes from each callee's actual writes, including its bounded work
area, rather than the overall signer's writable scratch region. -/
theorem checks_ok {p : Params} {S : Nat} {σ s : State} {t : Nat} {f : Poly}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : PairedRoots S s)
    (h : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1)
    (cache : PolyIs s.mem (pa s t4P) f) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) s fun u=>
      (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ PairedRoots S u ∧
      PolyIs u.mem (pa u t4P) f := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks
    Impl.MlDsa.AArch64.Sign.Optimized.pairedChecksPrefix
  refine WP.seq (WP.seq (WP.seq (WP.mono (challenge_ok hp ⟨roots,cache⟩ h h1) fun a ha=>?_)))
  refine WP.seq (WP.mono (init_ok hp hc ha.2 ha.1) fun b hb=>?_)
  refine WP.mono (optimizedZ_paired_vector_ok hp hb.2 hb.1) fun c hcstate=>?_
  refine WP.mono (optimizedR0_paired_vector_ok hp hcstate.2 (positiveIR_of_IZ hcstate.1)) fun d hd=>?_
  refine WP.seq (WP.mono (optimizedHint_paired_vector_ok hp hd.2 (positiveIH_of_IR hd.1)) fun e he=>?_)
  refine WP.seq (WP.mono (ones_ok hp hc he.2 he.1) fun a ha=>?_)
  exact WP.mono (branch_ok hp hc ha.2 ha.1) fun u hu=>⟨hu.1,hu.2.roots,hu.2.cache⟩

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks
