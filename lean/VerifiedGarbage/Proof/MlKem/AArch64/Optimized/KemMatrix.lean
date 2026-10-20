module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall

/-! # The complete paired encryption matrix satisfies the existing invariant -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64
variable {P : KemLay} {L : Layout}

theorem paired_matrix_ok {w16 : Bool} {s₀ s : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte}
    (h : BInvW w16 P L s₀ mA ρ 0 s) (tb : MatrixTable P L s₀ s) :
    WP isa (Impl.MlKem.AArch64.Paired.matrix P false w16) s fun t =>
      BInvW w16 P L s₀ mA ρ (P.k*P.k) t ∧ MatrixTable P L s₀ t := by
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
    refine WPs.mono (WPs.range (I := fun i t => BInvW w16 P L s₀ mA ρ (2*i) t ∧ MatrixTable P L s₀ t)
      (fun i hi t ht => ?_) ⟨h,tb⟩) fun t ht => ?_
    · refine WP.mono (paired_step hp (by omega : 2*i+1<P.k*P.k) ht.1 ht.2) fun u hu => ?_
      simpa only [Nat.mul_add,Nat.mul_one] using hu
    · by_cases ho : P.k*P.k%2=1
      · rw [ite_eq_left ho]
        apply WPs.single
        rw [Paired.lastSample_eq]
        have idx : 2*(P.k*P.k/2)=P.k*P.k-1 := by omega
        rw [idx] at ht
        refine WP.mono (singleton_step hp (by omega : P.k*P.k-1<P.k*P.k) ht.1 ht.2) fun u hu => ?_
        simpa only [Nat.sub_add_cancel hn] using hu
      · rw [ite_eq_right ho]
        have idx : 2*(P.k*P.k/2)=P.k*P.k := by omega
        simpa only [WPs,idx] using ht

end VG.Proof.MlKem.AArch64.Kem
