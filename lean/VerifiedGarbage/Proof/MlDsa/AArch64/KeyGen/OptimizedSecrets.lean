import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretGroup

/-! ## From `OptimizedSecretTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.Optimized

theorem secretSeeds_taint (nonce : Nat→Nat) : ∃h,
    (taint.check (Taint.ofRegs [.x28]) (.block (secretSeedsCode nonce)) h).isSome=true :=
  ⟨.block [],by with_unfolding_all rfl⟩

theorem secretSeeds_tr {p : Params} (hF : PFacts p) {S r : Nat} (nonce : Nat→Nat) :
    RelCT isa (R p S (KSamp p · (p.k*p.ℓ) r)) (.block (secretSeedsCode nonce)) (fun _ _=>True) := by
  obtain ⟨_,hc⟩:=secretSeeds_taint nonce
  exact rel_of (taintRel [.x28] (fun _ _ h=>Two.x28 h) hc)
    (fun _ _ _ _ hp hq pub hs ht=>kc_two hF hp hq pub hs.k1.kc ht.k1.kc)

theorem seeds_leak {p : Params} {S r n : Nat} (hn : n=3∨n=4) (hr : r+n≤p.ℓ+p.k)
    {σ τ s t : State} (pub : kgPub p S σ τ)
    (hs : SecretSeeds p σ r (fun i=>r+secretLane n i) 4 s)
    (ht : SecretSeeds p τ r (fun i=>r+secretLane n i) 4 t) :
    rejBoundedFourLeak p.η s.mem (pa s (sc 1408))=rejBoundedFourLeak p.η t.mem (pa t (sc 1408)) := by
  unfold rejBoundedFourLeak
  rw [List.flatMap_def,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i hi
  have hi4:=List.mem_range.mp hi
  rw [sc_add,sc_add,hs.done i hi4,ht.done i hi4]
  exact rej_pub pub (by have:=secretLane_lt (i := i) hn; omega)

theorem group_tr (c : Impl.Sha3.AArch64.Callee) {p : Params} (hF : PFacts p)
    {S r n : Nat} (hn : n=3∨n=4) (hr : r+n≤p.ℓ+p.k) :
    RelCT isa (R p S (KSamp p · (p.k*p.ℓ) r)) (groupCode c p r n) (fun _ _=>True) := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hη : p.η=2∨p.η=4 := by rcases hF.eta with h|h; exact Or.inl h.1; exact Or.inr h.1
  unfold groupCode
  refine RelCT.seq (relInv
    (fun _ _ hp hs=>secretSeeds_ok hF hp (by omega)
      (fun i hi=>by have:=secretLane_lt (i := i) hn; omega) hs)
    (secretSeeds_tr hF _)) ?_
  have hseed : inB (kgR++kgW p) (sc 1408) 264=true := by layd
  have hout : inB (kgR++kgW p) (sP p r) 4096=true := by lay
  have hwork : inB (kgR++kgW p) (sc (oR4 p)) 8192=true := by layd
  have hb0 := ptr_bs (kgOk p) hseed
  have hb1 := ptr_bs (kgOk p) hout
  have hb2 := ptr_bs (kgOk p) hwork
  refine RelCT.seq (BoundedFour.samplerAt_tr (S := S) c.pairedSha3 hη
    (ptr_ok (ptr_kept (kgOk p) hseed)) (ptr_ok (ptr_kept (kgOk p) hout))
    (ptr_ok (ptr_kept (kgOk p) hwork)) ?_) ?_
  · intro s t ⟨σ,τ,hp,hq,pub,hs,ht⟩
    have H:=kc_two hF hp hq pub hs.ks.k1.kc ht.ks.k1.kc
    exact ⟨boundedReady hF H.lx (by omega),boundedReady hF H.ly (by omega),
      H.same.pa hb0,H.same.pa hb1,H.same.pa hb2,H.same.2,seeds_leak hn hr pub hs ht⟩
  · exact block_nomem_tr (fun i hi _=>by
      simp only [and24,List.mem_singleton] at hi; subst i; rfl)

theorem group_piece (c : Impl.Sha3.AArch64.Callee) {p : Params} (hF : PFacts p)
    {S r n : Nat} (hn : n=3∨n=4) (hr : r+n≤p.ℓ+p.k) :
    Piece p S (KSamp p · (p.k*p.ℓ) r) (KSamp p · (p.k*p.ℓ) (r+n)) (groupCode c p r n) :=
  ⟨fun _ _ hp hs=>group_ok c hF hp hn hr hs,group_tr c hF hn hr⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedSecrets.lean` -/

section

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

end
