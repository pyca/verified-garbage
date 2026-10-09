import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretTiming

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call

theorem secretGroup_eq (c : Impl.Sha3.AArch64.Callee) (p : Params) (g : Nat) :
    VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretGroup c p g=groupCode c p (4*g) 4 := by
  have he : secretSeedsCode (fun i=>4*g+secretLane 4 i)=
      (List.range 4).flatMap (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretSeedSlot (4*g)) := by
    unfold secretSeedsCode
    rw [List.flatMap_def,List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    simp only [secretLane,ite_eq_left (List.mem_range.mp hi)]
    rfl
  unfold VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretGroup groupCode
  rw [he]

theorem secretTailThree_eq (c : Impl.Sha3.AArch64.Callee) (p : Params) :
    VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretTailThree c p=
      groupCode c p (4*((p.ℓ+p.k)/4)) 3 := by
  have he : secretSeedsCode (fun i=>4*((p.ℓ+p.k)/4)+secretLane 3 i)=
      (List.range 4).flatMap (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretTailSlot (4*((p.ℓ+p.k)/4))) := by
    unfold secretSeedsCode
    rw [List.flatMap_def,List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    have hi4:=List.mem_range.mp hi
    unfold secretLane VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretTailSlot
    by_cases hi3 : i=3
    · subst i; rfl
    · dsimp only
      simp only [ite_eq_left (by omega : i<3),ite_eq_right hi3]
  unfold VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretTailThree groupCode
  rw [he]

theorem secretGroup_piece (c : Impl.Sha3.AArch64.Callee) {p : Params} (hF : PFacts p)
    {S g : Nat} (hg : 4*(g+1)≤p.ℓ+p.k) :
    Piece p S (KSamp p · (p.k*p.ℓ) (4*g)) (KSamp p · (p.k*p.ℓ) (4*(g+1)))
      (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretGroup c p g) := by
  rw [secretGroup_eq]
  have he : 4*(g+1)=4*g+4 := by omega
  rw [he] at hg ⊢
  exact group_piece c hF (Or.inr rfl) hg


theorem secrets_piece (c : Impl.Sha3.AArch64.Callee) {p : Params} (hF : PFacts p)
    (hm : (p.ℓ+p.k)%4=0∨(p.ℓ+p.k)%4=3) (S : Nat) :
    Piece p S (KSamp p · (p.k*p.ℓ) 0) (KSamp p · (p.k*p.ℓ) (p.ℓ+p.k))
      (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretsWith c p) := by
  have hg : Piece p S (KSamp p · (p.k*p.ℓ) 0)
      (KSamp p · (p.k*p.ℓ) (4*((p.ℓ+p.k)/4)))
      (seqR (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretGroup c p) 0 ((p.ℓ+p.k)/4)) := by
    simpa only [Nat.mul_zero,Nat.zero_add] using Piece.seqR (S := S) (I := fun g σ s=>KSamp p σ (p.k*p.ℓ) (4*g) s) ((p.ℓ+p.k)/4) 0
      (fun g _ hg=>secretGroup_piece c hF (by omega))
  unfold VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretsWith
  apply Piece.seq hg
  split
  · rename_i hmod
    rw [secretTailThree_eq]
    have he : 4*((p.ℓ+p.k)/4)+3=p.ℓ+p.k := by omega
    simpa only [he] using group_piece c hF (S := S) (r := 4*((p.ℓ+p.k)/4))
      (n := 3) (Or.inl rfl) (by omega)
  · rename_i hmod
    have he : 4*((p.ℓ+p.k)/4)=p.ℓ+p.k := by omega
    rw [he]
    exact ⟨fun _ _ _ hs=>WP.block_nil hs,block_nomem_tr (fun _ hi _=>False.elim (List.not_mem_nil hi))⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
