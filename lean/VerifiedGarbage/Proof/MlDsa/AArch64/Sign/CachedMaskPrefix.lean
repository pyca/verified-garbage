import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskCopy
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedCommitment

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.Sign
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem cache_keep {p : Params} {S : Nat} {σ s u : State} {t : Nat}
    (L : Lay S (sgR p) (sgW p) s) (h : t=0 ∨ Mask p σ t s)
    {ws : List (Ptr×Nat)} (hP : PPostB S s u ws)
    (hc : keepB (sgR p) (sgW p) ws t4P 1024=true) : t=0 ∨ Mask p σ t u := by
  rcases h with h|h
  · exact .inl h
  · exact .inr (L.keepPoly hP hc h)

def pairCacheChk (p : Params) (r : Nat) : Bool :=
  keepB (sgR p) (sgW p) (pairSeedWrites 0) t4P 1024 &&
  keepB (sgR p) (sgW p) (pairSeedWrites 1) t4P 1024 &&
  keepB (sgR p) (sgW p) [(yP p r,1024),(yP p (r+1),1024),(sc (oR4 p),8192)] t4P 1024 &&
  keepB (sgR p) (sgW p) [(yhP p r,1024)] t4P 1024 &&
  keepB (sgR p) (sgW p) [(yhP p (r+1),1024)] t4P 1024

theorem pairCacheChk_ok {p : Params} (hp : p=mlDsa65∨p=mlDsa87) :
    (List.range (p.ℓ/2)).all (fun j => pairCacheChk p (2*j))=true := by
  rcases hp with rfl|rfl <;> decide

theorem finishCached_ok {p : Params} {S : Nat} {σ s : State} {t n r : Nat}
    (hr : r<n) (hc : positiveFinishChk p n r=true) (h : PositiveICm p S σ t r s)
    (hy : Fam s (yBase p) n (Yv p σ (p.ℓ*t))) (hm : t=0 ∨ Mask p σ t s)
    (hk : keepB (sgR p) (sgW p) [(yhP p r,1024)] t4P 1024=true) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p r) s fun u =>
      (PositiveICm p S σ t (r+1) u ∧ Fam u (yBase p) n (Yv p σ (p.ℓ*t))) ∧
      (t=0 ∨ Mask p σ t u) := by
  have hw := positiveFinish_ok hr hc h hy
  simp only [positiveFinishChk,optimizedMaskChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ho,hi⟩,hout⟩,hd⟩,_⟩,_⟩,_⟩,_⟩ := hc
  have hf : PolyIs s.mem (pa s (yP p r)) (Yv p σ (p.ℓ*t) r) := hy r hr
  have ht : ForwardRoots s (pa s (yhP p r)) :=
    ⟨h.l.k.d.roots.nttTableAt (h.l.st.lay.inW hout),h.l.k.d.roots.forward.readable⟩
  obtain ⟨tr,u,he,hu⟩ := hw
  obtain ⟨tr',u',he',hu'⟩ := positiveNttOutAt_layout h.l.st.lay ho hi hout hd ht hf.1
  obtain ⟨_,rfl⟩ := Exec.det he he'
  exact ⟨tr,u,he,hu,cache_keep h.l.st.lay hm hu'.1 hk⟩

theorem pairCached_ok {D : Nat}
    {nm : String} {cd : Prog isa} (C : CalleeOk D cd (expandMaskPairContract AArch64.abi D))
    {p : Params} {σ s : State} {t r : Nat} (hc : positivePairStepChk p r=true)
    (h : PositiveICm p D σ t r s) (hm : t=0 ∨ Mask p σ t s)
    (hcache : pairCacheChk p r=true) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p nm cd r) s (fun u => PositiveICm p D σ t (r+2) u ∧ (t=0 ∨ Mask p σ t u)) := by
  simp only [pairCacheChk,Bool.and_eq_true,and_assoc] at hcache
  obtain ⟨ck0,ck1,ckc,ckf0,ckf1⟩ := hcache
  simp only [positivePairStepChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cs0,cs1,ck,cm,ci,cf0,cf1,hg⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.Optimized.maskPairR
  refine WP.seq (WP.mono (positivePairSeed_ok cs0 h) fun a ⟨hA,hpa,ha⟩ => ?_)
  have ma := cache_keep h.l.st.lay hm hpa ck0
  refine WP.seq (WP.mono (positivePairSeed_ok cs1 hA) fun b ⟨hB,hb,hseed1⟩ => ?_)
  have mb := cache_keep hA.l.st.lay ma hb ck1
  have hseed0 : bytesAt b.mem (pa b (sc oMP)) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+r) 2 := by
    have hkeep := hA.l.st.lay.keepBytes hb ck
    simp only [Nat.mul_zero,Nat.add_zero] at ha
    rw [hkeep]
    exact ha
  have hseed1' : bytesAt b.mem (pa b (sc oMP)+66) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+(r+1)) 2 := by
    change bytesAt b.mem (pa b (sc (oMP+66))) 66=_ at hseed1
    rw [← pa_sc_add] at hseed1
    exact hseed1
  refine WP.seq (WP.mono_syms (maskPairAt_ok hB.l.st.lay.s64 C hB.l.st.lay cm hg)
    fun c ⟨hcP,_,hy0,hy1⟩ hsy => ?_)
  rw [hseed0] at hy0
  rw [hseed1'] at hy1
  have mc := cache_keep hB.l.st.lay mb hcP ckc
  have hC := hB.step hcP hsy ci
  have hy : Fam c (yBase p) (r+2) (Yv p σ (p.ℓ*t)) := by
    refine Fam.snoc (Fam.snoc hC.y ?_) ?_
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy0
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy1
  refine WP.seq (WP.mono (finishCached_ok (by omega) cf0 hC hy mc ckf0) fun d ⟨⟨hD,hyD⟩,md⟩ => ?_)
  exact WP.mono (finishCached_ok (by omega) cf1 hD hyD md ckf1) fun _ hu => ⟨hu.1.1,hu.2⟩


theorem prefix_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65∨p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveIL p S σ t s) (hm : t=0 ∨ Mask p σ t s) :
    WP isa (seqR (fun j => Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p
      "vg_mldsa_expand_mask_pair_sha3" P.expandMaskPair (2*j)) 0 (p.ℓ/2)) s fun u =>
      PositiveICm p S σ t (2*(p.ℓ/2)) u ∧ (t=0 ∨ Mask p σ t u) := by
  have h3 : Ok3 p := hp.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
  have hc := positiveMasksChk_ok h3
  simp only [positiveMasksChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  have hk := pairCacheChk_ok hp
  simp only [List.all_eq_true,List.mem_range] at hk
  simpa only [Nat.zero_add] using
    seqR_ok (I := fun j u => PositiveICm p S σ t (2*j) u ∧ (t=0 ∨ Mask p σ t u))
      (p.ℓ/2) 0 (fun j _ hj u hu => by
        simpa only [Nat.mul_add,Nat.mul_one] using
          pairCached_ok hP.expandMaskPair (hc.1 j (by omega)) hu.1 hu.2 (hk j (by omega)))
      s ⟨⟨h,fun _ h => by omega,fun _ h => by omega⟩,hm⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached
