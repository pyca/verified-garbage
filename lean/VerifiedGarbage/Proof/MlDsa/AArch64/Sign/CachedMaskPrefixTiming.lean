import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskPrefix
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)

theorem pairCached_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} {r t : Nat}
    (hc : positivePairStepChk p r=true) (hk : pairCacheChk p r=true) {E : State→State→Prop} :
    RelCT isa (RootRS p S E fun σ s => PositiveICm p S σ t r s ∧ (t=0 ∨ Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p "vg_mldsa_expand_mask_pair_sha3" P.expandMaskPair r)
      (RootRS p S E fun σ s => PositiveICm p S σ t (r+2) s ∧ (t=0 ∨ Mask p σ t s)) := by
  apply liftRootR (fun _ _ _ h => pairCached_ok hP.expandMaskPair hc h.1 h.2 hk)
  apply RelCT.mono (positivePairR_tr hP.expandMaskPair hc (t := t) (E := E))
  · intro x y h
    exact ⟨h.1.mono (fun _ _ h => h) (fun _ _ h => h.1),h.2.1⟩
  · intro _ _ _
    trivial

theorem prefix_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65∨p=mlDsa87) {t : Nat} {E : State→State→Prop} :
    RelCT isa (RootRS p S E fun σ s => PositiveIL p S σ t s ∧ (t=0 ∨ Mask p σ t s))
      (seqR (fun j => Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p
        "vg_mldsa_expand_mask_pair_sha3" P.expandMaskPair (2*j)) 0 (p.ℓ/2))
      (RootRS p S E fun σ s => PositiveICm p S σ t (2*(p.ℓ/2)) s ∧ (t=0 ∨ Mask p σ t s)) := by
  have h3 : Ok3 p := hp.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
  have hc := positiveMasksChk_ok h3
  simp only [positiveMasksChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  have hk := pairCacheChk_ok hp
  simp only [List.all_eq_true,List.mem_range] at hk
  refine RelCT.mono (seqR_tr (Q := fun j => RootRS p S E fun σ s =>
    PositiveICm p S σ t (2*j) s ∧ (t=0 ∨ Mask p σ t s)) (p.ℓ/2) 0 (fun j _ hj => ?_))
    (fun _ _ h => h.mono (fun _ _ h => ⟨⟨h.1,fun _ h => by omega,fun _ h => by omega⟩,h.2⟩))
    (fun _ _ h => by simpa only [Nat.zero_add] using h)
  simpa only [Nat.mul_add,Nat.mul_one] using pairCached_tr hP (hc.1 j (by omega)) (hk j (by omega)) (t := t) (E := E)

end VG.Proof.MlDsa.AArch64.Sign.Cached
