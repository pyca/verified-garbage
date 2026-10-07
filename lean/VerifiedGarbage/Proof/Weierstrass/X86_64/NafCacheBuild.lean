import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCacheBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState

/-! Cached powers are canonical Montgomery values and preserve the source table. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem nafCachePair_fields_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hn : M.n=4) (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {ptbl tbl i : Nat}
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hZ : ptbl+96*i+64∈V)
    (h2 : Sl (tbl+64*i)) (h3 : Sl (tbl+64*i+32)) :
    WP isa (Naf.cachePair M ptbl tbl i) s fun t =>
      ProgKeep M base ((Naf.cachePairOps ptbl tbl i).map FOp.out) s t ∧
      Inv M base size m Sl (validAfter (Naf.cachePairOps ptbl tbl i) V)
        (runOps (Naf.cachePairOps ptbl tbl i) E) t := by
  have hS : ∀ op∈Naf.cachePairOps ptbl tbl i,∀ x∈op.out::op.ins,Sl x := by
    intro op hop x hx
    simp only [Naf.cachePairOps,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    · rcases hx with rfl|rfl|rfl
      · exact h2
      · exact hI.sl _ hZ
      · exact hI.sl _ hZ
    · rcases hx with rfl|rfl|rfl
      · exact h3
      · exact h2
      · exact hI.sl _ hZ
  have hR : readsOk (Naf.cachePairOps ptbl tbl i) V=true := by
    simp [Naf.cachePairOps,readsOk,FOp.ins,FOp.out,hZ]
  rw [Naf.cachePair]
  split
  · exact WP.mono (ForwardField.program_ok hn hL hm _ hI hS hR (fun _ h => by cases h))
      (fun _ h => ⟨h.1,h.2.1⟩)
  · exact (fprogB_wp _ _).mpr (fprog_ok hL hm _ hI hS hR)

theorem nafCachePair_ok {M : Mod} {base : Addr} {size : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hn : M.n=4) (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) {ptbl tbl i : Nat}
    (hSep : tbl+64*(i+1)≤ptbl ∨ ptbl+96*(i+1)≤tbl)
    {V : List Nat} {E : Nat → Fin C.p} {s : State}
    (hI : Inv M base size C.p Sl V E s) (hZ : ptbl+96*i+64∈V)
    (h2 : Sl (tbl+64*i)) (h3 : Sl (tbl+64*i+32)) :
    WP isa (Naf.cachePair M ptbl tbl i) s fun t =>
      ProgKeep M base [tbl+64*i,tbl+64*i+32] s t ∧
      Inv M base size C.p Sl ([tbl+64*i,tbl+64*i+32]++V) (tmv C M.n base t) t ∧
      tmv C M.n base t (tbl+64*i)=E (ptbl+96*i+64)*E (ptbl+96*i+64) ∧
      tmv C M.n base t (tbl+64*i+32)=
        tmv C M.n base t (tbl+64*i)*E (ptbl+96*i+64) := by
  have hz2 : ptbl+96*i+64≠tbl+64*i := by omega
  have h23 : tbl+64*i≠tbl+64*i+32 := by omega
  have hp := nafCachePair_fields_ok hn hL hm hI hZ h2 h3
  refine WP.mono hp fun t ⟨kt,it⟩ => ?_
  have iv : Inv M base size C.p Sl ([tbl+64*i,tbl+64*i+32]++V)
      (runOps (Naf.cachePairOps ptbl tbl i) E) t := it.sub (by
    intro x hx
    simp only [Naf.cachePairOps,validAfter,FOp.out,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hx ⊢
    grind)
  have v2 := iv.val (tbl+64*i) (by simp)
  have v3 := iv.val (tbl+64*i+32) (by simp)
  simp only [Naf.cachePairOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
    Function.update_self,Function.update_of_ne hz2,Function.update_of_ne h23] at v2 v3
  refine ⟨kt,iv.to_tmv,v2,?_⟩
  unfold tmv
  rw [v2]
  exact v3

def cacheTableSlots (tbl : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => [tbl+64*k,tbl+64*k+32]++cacheTableSlots tbl k

theorem mem_cacheTableSlots {x tbl k : Nat} :
    x∈cacheTableSlots tbl k ↔ ∃ i<k,x=tbl+64*i ∨ x=tbl+64*i+32 := by
  induction k with
  | zero => simp [cacheTableSlots]
  | succ k ih =>
    simp only [cacheTableSlots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,ih]
    constructor
    · rintro ((h|h)|⟨i,hi,h⟩)
      · exact ⟨k,by omega,Or.inl h⟩
      · exact ⟨k,by omega,Or.inr h⟩
      · exact ⟨i,by omega,h⟩
    · rintro ⟨i,hi,h⟩
      by_cases he : i=k
      · subst i; exact Or.inl h
      · exact Or.inr ⟨i,by omega,h⟩

theorem nafCacheTable_ok {M : Mod} {base : Addr} {size : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hn : M.n=4) (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (k : Nat) {ptbl tbl : Nat}
    (hSep : tbl+64*k≤ptbl ∨ ptbl+96*k≤tbl)
    {V : List Nat} {E : Nat → Fin C.p} {s : State}
    (hI : Inv M base size C.p Sl V E s) (hZ : ∀ i<k,ptbl+96*i+64∈V)
    (hSl : ∀ i<k,Sl (tbl+64*i) ∧ Sl (tbl+64*i+32)) :
    WP isa (Naf.cacheTable M ptbl tbl k) s fun t =>
      ProgKeep M base (cacheTableSlots tbl k) s t ∧
      Inv M base size C.p Sl (cacheTableSlots tbl k++V) (tmv C M.n base t) t ∧
      ∀ i<k,tmv C M.n base t (tbl+64*i)=E (ptbl+96*i+64)*E (ptbl+96*i+64) ∧
        tmv C M.n base t (tbl+64*i+32)=tmv C M.n base t (tbl+64*i)*E (ptbl+96*i+64) := by
  induction k with
  | zero => exact WP.block_nil ⟨ProgKeep.refl _ _ _ s,hI.to_tmv,fun _ h => by omega⟩
  | succ k ih =>
    rw [Naf.cacheTable]
    apply WP.seq
    refine WP.mono (ih (by omega) (fun i hi => hZ i (by omega))
      (fun i hi => hSl i (by omega))) fun u ⟨ku,iu,hu⟩ => ?_
    have hW : ∀ x∈cacheTableSlots tbl k,Sl x := by
      intro x hx
      obtain ⟨j,hj,rfl|rfl⟩ := mem_cacheTableSlots.mp hx
      · exact (hSl j (by omega)).1
      · exact (hSl j (by omega)).2
    have zu : tmv C M.n base u (ptbl+96*k+64)=E (ptbl+96*k+64) := by
      unfold tmv
      rw [ku.slot hL hI.scr hW (hI.sl _ (hZ k (by omega))) ?_,hI.val _ (hZ k (by omega))]
      intro hz
      obtain ⟨j,hj,hj'⟩ := mem_cacheTableSlots.mp hz
      omega
    refine WP.mono (nafCachePair_ok hn hL hm hSep iu
      (List.mem_append_right _ (hZ k (by omega)))
      (hSl k (by omega)).1 (hSl k (by omega)).2) fun t ⟨kt,it,h2,h3⟩ => ?_
    have hWp : ∀ x∈[tbl+64*k,tbl+64*k+32],Sl x := by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact (hSl k (by omega)).1
      · exact (hSl k (by omega)).2
    have old (x : Nat) (hx : Sl x) (hnot : x∉[tbl+64*k,tbl+64*k+32]) :
        tmv C M.n base t x=tmv C M.n base u x := by
      unfold tmv
      rw [kt.slot hL iu.scr hWp hx hnot]
    refine ⟨(ku.mono (fun _ h => List.mem_append_right _ h)).trans
      (kt.mono (fun _ h => List.mem_append_left _ h)),?_,fun i hi => ?_⟩
    · simpa only [cacheTableSlots,List.append_assoc] using it
    · by_cases he : i=k
      · subst i
        rw [zu] at h2 h3
        exact ⟨h2,h3⟩
      · have hik : i<k := by omega
        have e2 := old (tbl+64*i) (hSl i hi).1 (by
          simp only [List.mem_cons,List.not_mem_nil,or_false]; omega)
        have e3 := old (tbl+64*i+32) (hSl i hi).2 (by
          simp only [List.mem_cons,List.not_mem_nil,or_false]; omega)
        rw [e2,e3]
        exact hu i hik

/-- Express each cache pair in terms of the source Z still in the resulting state. -/
theorem nafCacheTable_current_ok {M : Mod} {base : Addr} {size : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hn : M.n=4) (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (k : Nat) {ptbl tbl : Nat}
    (hSep : tbl+64*k≤ptbl ∨ ptbl+96*k≤tbl)
    {V : List Nat} {E : Nat → Fin C.p} {s : State}
    (hI : Inv M base size C.p Sl V E s) (hZ : ∀ i<k,ptbl+96*i+64∈V)
    (hSl : ∀ i<k,Sl (tbl+64*i) ∧ Sl (tbl+64*i+32)) :
    WP isa (Naf.cacheTable M ptbl tbl k) s fun t =>
      ProgKeep M base (cacheTableSlots tbl k) s t ∧
      Inv M base size C.p Sl (cacheTableSlots tbl k++V) (tmv C M.n base t) t ∧
      ∀ i<k,tmv C M.n base t (tbl+64*i)=
          tmv C M.n base t (ptbl+96*i+64)*tmv C M.n base t (ptbl+96*i+64) ∧
        tmv C M.n base t (tbl+64*i+32)=
          tmv C M.n base t (tbl+64*i)*tmv C M.n base t (ptbl+96*i+64) := by
  refine WP.mono (nafCacheTable_ok hn hL hm k hSep hI hZ hSl) fun t ⟨kt,it,ht⟩ =>
    ⟨kt,it,fun i hi => ?_⟩
  have hW : ∀ x∈cacheTableSlots tbl k,Sl x := by
    intro x hx
    obtain ⟨j,hj,rfl|rfl⟩ := mem_cacheTableSlots.mp hx
    · exact (hSl j hj).1
    · exact (hSl j hj).2
  have ze : tmv C M.n base t (ptbl+96*i+64)=E (ptbl+96*i+64) := by
    unfold tmv
    rw [kt.slot hL hI.scr hW (hI.sl _ (hZ i hi)) ?_,hI.val _ (hZ i hi)]
    intro hz
    obtain ⟨j,hj,hj'⟩ := mem_cacheTableSlots.mp hz
    omega
  rw [ze]
  exact ht i hi

end VG.Proof.Weierstrass.X86_64
