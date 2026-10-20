module
public import VerifiedGarbage.Proof.MlKem.AArch64.KgB
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable

import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixLast
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPair

/-! # The complete paired key-generation matrix satisfies the existing invariant -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64
variable {P : KemLay}

theorem paired_matrix_ok {w16 : Bool} {s₀ s : State} (hp : Pre P s₀)
    (h : BInvW w16 P s₀ 0 s) (tb : MatrixTable P s₀ s) :
    WP isa (Impl.MlKem.AArch64.Paired.matrix P true w16) s fun t =>
      BInvW w16 P s₀ (P.k*P.k) t ∧ MatrixTable P s₀ t := by
  have hk : 0<P.k := hp.wf.facts.1
  have hn : 0<P.k*P.k := Nat.mul_pos hk hk
  apply WPs.seqs
  · intro hh
    have parts := List.append_eq_nil_iff.mp hh
    by_cases ho : P.k*P.k%2=1
    · simpa only [ite_eq_left ho,List.cons_ne_nil] using parts.2
    · have np : 0<P.k*P.k/2 := by omega
      exact map_range_ne_nil np _ parts.1
  · apply WPs.append
    refine WPs.mono (WPs.range (I := fun i t => BInvW w16 P s₀ (2*i) t ∧ MatrixTable P s₀ t)
      (fun i hi t ht => ?_) ⟨h,tb⟩) fun t ht => ?_
    · refine WP.mono (matrix_pair hp (by omega : 2*i+1<P.k*P.k) ht.1 ht.2) fun u hu => ?_
      simpa only [Nat.mul_add,Nat.mul_one] using hu
    · by_cases ho : P.k*P.k%2=1
      · rw [ite_eq_left ho]
        apply WPs.single
        rw [Paired.lastSample_eq]
        have idx : 2*(P.k*P.k/2)=P.k*P.k-1 := by omega
        rw [idx] at ht
        refine WP.mono (matrix_singleton hp (by omega : P.k*P.k-1<P.k*P.k) ht.1 ht.2) fun u hu => ?_
        simpa only [Nat.sub_add_cancel hn] using hu
      · rw [ite_eq_right ho]
        have idx : 2*(P.k*P.k/2)=P.k*P.k := by omega
        simpa only [WPs,idx] using ht

end VG.Proof.MlKem.AArch64.KeyGen
