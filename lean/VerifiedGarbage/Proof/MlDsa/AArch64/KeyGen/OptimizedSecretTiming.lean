import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretGroup

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
  have hseed : inB (kgR++kgW p) (sc 1408) 264=true := by lay
  have hout : inB (kgR++kgW p) (sP p r) 4096=true := by lay
  have hwork : inB (kgR++kgW p) (sc (oR4 p)) 8192=true := by lay
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
