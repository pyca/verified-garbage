import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheEntryTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming

/-! Timing of a peer digit with its precomputed Jacobian powers. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
  List.not_mem_nil,or_false] at * <;> grind))

structure JointCachedChecks (c : Joint.Cfg) : Prop where
  read : RegCT [.rdi,.rbx] (.block (Naf.digitRead c.K))
  entry : RegCT [.rdi,.r8] (Naf.signedCachedEntry c.K c.cache c.selected)
  add : CachedJacChecks c.K c.K.R c.K.E c.K.D c.selected
  copy : ScratchCT (.block (copyPt c.K.M.n c.K.R c.K.D))

theorem jointCachedSum_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hc : JointCachedChecks c)
    (h2 : E c.selected=E c.K.E.z*E c.K.E.z)
    (h3 : E (c.selected+8*c.K.M.n)=E c.selected*E c.K.E.z) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) (cachedSlots c.K.M.n c.K.E c.selected++jointLive c) E)
      (.seq (CachedJac.add c.K c.K.R c.K.E c.K.D c.selected) (.block (copyPt c.K.M.n c.K.R c.K.D)))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have sl : ∀ x∈(rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E)++[c.selected,c.selected+8*c.K.M.n],x∈jointSlots c := by intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E++[c.selected,c.selected+8*c.K.M.n],x∈cachedSlots c.K.M.n c.K.E c.selected++jointLive c := by intro x hx; jslots
  apply RelCT.seq (cachedJacAdd_relCT hL.lookup.layout.lay hm hc.add
    hL.addApart hL.cache2Apart hL.cache3Apart sl vr hOne h2 h3)
  apply RelCT.exists_
  intro E'
  have cp := copyPoint_relCT (base:=base) (E:=E') hL.lookup.layout.lay
    (o:=c.K.R) (q:=c.K.D) (by intro x hx; jslots)
    (V:=jacCoords c.K.D++(cachedSlots c.K.M.n c.K.E c.selected++jointLive c))
    (by intro x hx; exact List.mem_append_left _ hx) hc.copy
  exact cp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun _ hx =>
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hx)))⟩)

theorem jointCachedDigit_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v j : Nat}
    {Q A : Point C} {External : State → Prop} {E : Nat → Fe C}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hj : j<64*c.K.M.n+1) (hc : JointCachedChecks c)
    (hExternal : ∀ s t,VG.Proof.X25519.X86_64.Keeps [.r8] s t → t.syms=s.syms → External s → External t) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v External A s ∧ JointCore c C base size Q u v External A t ∧
      s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
      (Joint.cachedDigit c)
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have hbytes : c.K.bits+j<size := by
    have hh := hL.lookup.layout.stableBounds (c.K.bits,64*c.K.M.n+1) (by simp [jointStableRanges])
    dsimp only at hh
    omega
  apply nafDigitBranch_relCT hbytes hc.read (fun _ hs => hs.stable.peer j hj)
    (fun s t hk st hs => hs.of_keeps hk (by decide) (hExternal s t hk st hs.external))
  intro hb s t ts tt s' t' ⟨hp,cs,_,s8,t8⟩ es et
  have hmag : FastNaf.magnitude 5 v j≠0 := fun he => hb ((FastNaf.byte_zero_iff 5 v j).mpr he)
  have hmagn : nafMagnitude (FastNaf.byte 5 v j)=FastNaf.magnitude 5 v j := FastNaf.byte_magnitude 5 v j
  have ha : 1≤nafMagnitude (FastNaf.byte 5 v j) := by rw [hmagn]; omega
  have hbound : nafMagnitude (FastNaf.byte 5 v j)≤15 := by
    rw [hmagn]; exact FastNaf.magnitude_le (Or.inl rfl) v j
  have ho : nafMagnitude (FastNaf.byte 5 v j)%2=1 := by
    rw [hmagn]; exact (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hmag
  let i := (nafMagnitude (FastNaf.byte 5 v j)-1)/2
  have hi : i<8 := by dsimp only [i]; omega
  have hq : ∀ x∈cachedSlots c.K.M.n (c.K.tblPt (i+1)) (c.cache+16*c.K.M.n*i),x∈jointLive c := by
    intro x hx
    apply jointStable_live c
    rcases List.mem_append.mp hx with hx|hx
    · exact jointStable_table c (by omega) (by omega) hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact jointStable_cache2 c hi
      · exact jointStable_cache3 c hi
  have same (x : Nat) (hx : x∈cachedSlots c.K.M.n (c.K.tblPt (i+1)) (c.cache+16*c.K.M.n*i)) :
      tmv C c.K.M.n base s x=E x := hp.1.val x (hq x hx)
  have point : CachedPoint c.K.M.n C E (c.K.tblPt (i+1)) (c.cache+16*c.K.M.n*i) (mul (2*(i+1)-1) Q) := by
    rw [CachedPoint,←same _ (by simp [cachedSlots,jacCoords]),
      ←same _ (by simp [cachedSlots,jacCoords]),←same _ (by simp [cachedSlots,jacCoords]),
      ←same _ (by simp [cachedSlots]),←same _ (by simp [cachedSlots])]
    exact ⟨cs.stable.table (i+1) (by omega) (by omega),cs.stable.cache2 i hi,cs.stable.cache3 i hi⟩
  have result := cachedEntryEnv_point (by have := hL.lookup.layout.n; omega) hL.lookup.exy hL.lookup.exz hL.lookup.selectedEntry point
  have zero : E c.K.zero=0 := by
    rw [←hp.1.val _ (by simp [jointLive,winRo])]
    exact cs.stable.zero
  have ds : ∀ x∈cachedSlots c.K.M.n c.K.E c.selected,x∈jointSlots c := by intro x hx; jslots
  have entry := nafSignedCachedEntry_relCT (base:=base) (E:=E)
    hL.lookup.layout.lay hL.lookup.layout.n hm ha hbound ho hL.lookup.exy hL.lookup.exz
    hL.lookup.tableSmall hL.lookup.cacheSmall hL.lookup.tableBound hL.lookup.cacheBound ds hq
    hL.lookup.entryTable hL.lookup.entryCache hL.lookup.selectedCache hL.lookup.selectedEntry
    (by simp [jointLive,winRo]) zero hL.lookup.zeroApart hc.entry
  exact (RelCT.seq entry (jointCachedSum_relCT hL hm hOne hc result.2.1 result.2.2))
    _ _ _ _ _ _ ⟨hp,s8,t8⟩ es et

end VG.Proof.Weierstrass.X86_64
