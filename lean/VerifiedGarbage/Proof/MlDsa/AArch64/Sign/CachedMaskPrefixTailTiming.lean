import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskCopy
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedCommitment
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskTail

/-! ## From `CachedMaskPrefix.lean` -/

section

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

end

/-! ## From `CachedMaskPrefixTiming.lean` -/

section

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

end

/-! ## From `CachedMaskPrefixTailTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlKem.AArch64 (Only wp_ldrx wp_nil)
open VG.Proof.MlDsa.Sign

private theorem seqIte_tr {P Q : State→State→Prop} {c : Cond} {a b d : Prog isa}
    (hc : ∀x y,P x y→isa.eval c x=isa.eval c y)
    (ha : RelCT isa (fun x y=>P x y ∧ isa.eval c x=some true) (.seq a d) Q)
    (hb : RelCT isa (fun x y=>P x y ∧ isa.eval c x=some false) (.seq b d) Q) :
    RelCT isa P (.seq (.ite c a b) d) Q := by
  intro x y tx ty u v hp ex ey
  have hcond := hc x y hp
  cases ex with
  | seq ex ed =>
    cases ey with
    | seq ey ef =>
      cases ex with
      | iteT hx ea =>
        cases ey with
        | iteT _ eb =>
          obtain ⟨he,hq⟩ := ha _ _ _ _ _ _ ⟨hp,hx⟩ (.seq ea ed) (.seq eb ef)
          exact ⟨by simpa only [List.cons_append] using congrArg (List.cons (.branch true)) he,hq⟩
        | iteF hy _ => rw [hcond,hy] at hx; cases hx
      | iteF hx ea =>
        cases ey with
        | iteT hy _ => rw [hcond,hy] at hx; cases hx
        | iteF _ eb =>
          obtain ⟨he,hq⟩ := hb _ _ _ _ _ _ ⟨hp,hx⟩ (.seq ea ed) (.seq eb ef)
          exact ⟨by simpa only [List.cons_append] using congrArg (List.cons (.branch false)) he,hq⟩

theorem loadIndex_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : p=mlDsa65∨p=mlDsa87) (h : PositiveICm p S σ t (p.ℓ-1) s) (hm : t=0∨Mask p σ t s) :
    WP isa (.block [.ldr .x .x9 .x28 oKAP]) s fun u =>
      (PositiveICm p S σ t (p.ℓ-1) u ∧ (t=0∨Mask p σ t u)) ∧ u.gpr .x9=BitVec.ofNat 64 (p.ℓ*t) := by
  have hk : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl <;> decide
  have hload : WP isa (.block [.ldr .x .x9 .x28 oKAP]) s fun a =>
      Only [.x9] s a ∧ a.gpr .x9=s.mem.readW (pa s (sc oKAP)) 64 :=
    wp_ldrx (t:=.x9) (n:=.x28) (off:=oKAP) (a:=pa s (sc oKAP))
    (by decide) rfl (h.l.st.lay.inR hk) fun a ha va=>wp_nil ⟨ha,va⟩
  refine WP.mono_syms hload fun u ⟨hu,hv⟩ hy => ?_
  have hP : PPostB S s u [] := postB_of_keep hu.keep (by decide) (by rw [hu.mem];exact Frame.refl _ _)
  exact ⟨⟨h.step hP hy (by rcases hp with rfl|rfl <;> decide),
    cache_keep h.l.st.lay hm hP (by rcases hp with rfl|rfl <;> decide)⟩,hv.trans h.l.kap⟩

theorem copyFinish_tr {p : Params} {S t : Nat} {E : State→State→Prop}
    (hp : p=mlDsa65∨p=mlDsa87) :
    RelCT isa (RootRS p S E fun σ s => PositiveICm p S σ t (p.ℓ-1) s ∧ Mask p σ t s)
      (.seq (Impl.MlDsa.AArch64.Sign.Cached.copyMask p)
        (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p (p.ℓ-1))) fun _ _ => True := by
  apply RelCT.seq (R := RootRS p S E fun σ s => PositiveICm p S σ t (p.ℓ-1) s ∧
    Fam s (yBase p) (p.ℓ-1+1) (Yv p σ (p.ℓ*t)))
  · apply liftRootR (fun _ _ _ h => copyMask_phase_ok (copyChk_ok hp) h.1 h.2)
    exact lrel_tr (hc := copyHint) (fun _ _ h=>h.1.lrel (fun _ _ h=>h.1.l.st)) (by rcases hp with rfl|rfl <;> taint_decide)
  · apply optimizedMaskFinish_tr (S := S) (show optimizedMaskChk p (p.ℓ-1)=true from by rcases hp with rfl|rfl <;> decide)
    intro x y h
    have L := h.1.lrel (fun _ _ h=>h.1.l.st)
    obtain ⟨σ,τ,_,_,_,_,ix,iy⟩ := h.1
    exact ⟨⟨σ,ix.1.l.st,ix.1.l.k.d.roots⟩,⟨τ,iy.1.l.st,iy.1.l.k.d.roots⟩,
      (ix.2 (p.ℓ-1) (by omega)).1,(iy.2 (p.ℓ-1) (by omega)).1,
      L.regs .x28 (by decide),L.sp,h.2.1⟩

private theorem assocBack {P Q : State→State→Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro x y tx ty u v hp ex ey
  cases ex with
  | seq ex ec =>
    cases ex with
    | seq ea eb =>
      cases ey with
      | seq ey fc =>
        cases ey with
        | seq fa fb =>
          obtain ⟨ht,hq⟩ := h _ _ _ _ _ _ hp (.seq ea (.seq eb ec)) (.seq fa (.seq fb fc))
          exact ⟨by simpa only [List.append_assoc] using ht,hq⟩

theorem tailMask_tr {P : Prims} {S t : Nat} {E : State→State→Prop}
    (hP : PrimsOk P S) {p : Params} (hp : p=mlDsa65∨p=mlDsa87) :
    RelCT isa (RootRS p S E fun σ s=>PositiveICm p S σ t (p.ℓ-1) s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.tailMask P p)
      (RootRS p S E (PositiveICm p S · t p.ℓ)) := by
  apply liftRootR (fun _ _ _ h=>tailMask_ok hP hp h.1 h.2)
  unfold Impl.MlDsa.AArch64.Sign.Cached.tailMask
  apply RelCT.seq (R := RootRS p S E fun σ s=>
    (PositiveICm p S σ t (p.ℓ-1) s ∧ (t=0∨Mask p σ t s)) ∧ s.gpr .x9=BitVec.ofNat 64 (p.ℓ*t))
  · apply liftRootR (fun _ _ _ h=>loadIndex_ok hp h.1 h.2)
    exact lrel_tr (fun _ _ h=>h.1.lrel (fun _ _ h=>h.1.l.st)) (by taint_decide)
  · apply seqIte_tr
    · intro x y h
      obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1
      change some (x.gpr .x9 != 0)=some (y.gpr .x9 != 0)
      rw [hx.2,hy.2]
    · apply RelCT.mono (copyFinish_tr hp)
      intro x y h
      apply RootRS.mono h.1
      intro σ s hs
      refine ⟨hs.1.1,hs.1.2.resolve_left ?_⟩
      intro ht
      obtain ⟨σ',τ,_,_,_,_,hx,_⟩ := h.1.1
      have he := h.2
      change some (x.gpr .x9 != 0)=some true at he
      rw [hx.2,ht,Nat.mul_zero] at he
      cases he
      · intro _ _ _; trivial
    · have cf : positiveMaskChk p (p.ℓ-1)=true := by rcases hp with rfl|rfl <;> decide
      apply assocBack
      apply RelCT.mono (positiveMaskR_tr hP cf)
      · intro x y h
        exact ⟨h.1.1.mono (fun _ _ h=>h) (fun _ _ hs=>hs.1.1),h.1.2.1⟩
      · intro _ _ _; trivial

theorem masks_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65∨p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveIL p S σ t s) (hm : t=0∨Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.masks P p) s (PositiveICm p S σ t p.ℓ) := by
  have hn : 2*(p.ℓ/2)=p.ℓ-1 := by rcases hp with rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Cached.masks
  refine WP.seq (WP.mono (prefix_ok hP hp h hm) fun u hu=>?_)
  rw [hn] at hu
  exact tailMask_ok hP hp hu.1 hu.2

theorem masks_tr {P : Prims} {S t : Nat} {E : State→State→Prop}
    (hP : PrimsOk P S) {p : Params} (hp : p=mlDsa65∨p=mlDsa87) :
    RelCT isa (RootRS p S E fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.masks P p)
      (RootRS p S E (PositiveICm p S · t p.ℓ)) := by
  have hn : 2*(p.ℓ/2)=p.ℓ-1 := by rcases hp with rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Cached.masks
  have hf := prefix_tr (E:=E) (t:=t) hP hp
  rw [hn] at hf
  exact RelCT.seq hf (tailMask_tr hP hp)

end VG.Proof.MlDsa.AArch64.Sign.Cached

end
