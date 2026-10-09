import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedR0

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem optimizedR0_paired_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (roots : PairedRoots S s) (h : PositiveIR p S σ t 0 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase p) s fun u =>
      PositiveIR p S σ t p.k u ∧ PairedRoots S u := by
  have heven : p.k%2=0 := by rcases hp with rfl|rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase
  rw [ite_eq_left heven]
  refine WP.seq (WP.mono (seqR_ok (I:=fun j s => PositiveIR p S σ t (2*j) s ∧ PairedRoots S s)
    (p.k/2) 0 (fun j _ hj a ha => ?_) s ⟨by simpa only [Nat.mul_zero] using h,roots⟩) ?_)
  · simpa only [Nat.mul_add,Nat.mul_one] using optimizedR0_pair_ok hp (by omega : 2*j+1<p.k) ha.2 ha.1
  · intro a ha
    have he : 2*(p.k/2)=p.k := by omega
    simp only [Nat.zero_add,he] at ha
    exact WP.block_nil ha

end VG.Proof.MlDsa.AArch64.Sign
