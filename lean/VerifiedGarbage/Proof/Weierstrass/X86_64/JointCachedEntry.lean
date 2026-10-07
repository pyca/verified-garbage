import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInvariant
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedPoint
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! Select a cached odd multiple while retaining the accumulator and both scalar streams. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
  List.not_mem_nil,or_false] at * <;> grind))

structure JointLookupLayout (c : Joint.Cfg) (size : Nat) : Prop where
  layout : JointLayout c size
  exy : c.K.E.y=c.K.E.x+32
  exz : c.K.E.z=c.K.E.x+64
  tableSmall : c.K.tbl<2^31
  cacheSmall : c.cache<2^31
  tableBound : c.K.tbl+768≤size
  cacheBound : c.cache+512≤size
  entryTable : c.K.E.x+96≤c.K.tbl ∨ c.K.tbl+768≤c.K.E.x
  entryCache : c.K.E.x+96≤c.cache ∨ c.cache+512≤c.K.E.x
  selectedCache : c.selected+64≤c.cache ∨ c.cache+512≤c.selected
  selectedEntry : c.selected+64≤c.K.E.x ∨ c.K.E.x+96≤c.selected
  zeroApart : c.K.zero∉cachedSlots c.K.E c.selected
  accumApart : ∀ x∈jacCoords c.K.R,x∉cachedSlots c.K.E c.selected

theorem jointStable_live (c : Joint.Cfg) : ∀ x∈jointStableFields c,x∈jointLive c := by
  intro x hx
  simp only [jointStableFields,jointLive,List.mem_append] at hx ⊢
  grind

theorem jointKeeps_prog {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    {rs : List Reg} (hk : Keeps rs s t) (hr : ∀ r∈rs,r∈clob M.n) :
    ProgKeep M base W s t :=
  ⟨fun r h => hk.1 r (fun h' => h (hr r h')),hk.2.2.1,hk.2.2.2,
    fun x _ _ => congrFun hk.2.1 x⟩

theorem jointCachedEntry_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v j : Nat}
    {Q A : Point C} {External : State → Prop} {s : State}
    (hL : JointLookupLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (h : JointCore c C base size Q u v External A s)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (hmag : FastNaf.magnitude 5 v j≠0)
    (h8 : s.gpr .r8=(FastNaf.byte 5 v j).setWidth 64) :
    WP isa (Naf.signedCachedEntry c.K c.cache c.selected) s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v External A t ∧
      Inv c.K.M base size C.p (·∈jointSlots c)
        (cachedSlots c.K.E c.selected++jointLive c) (tmv C c.K.M.n base t) t ∧
      CachedPoint C (tmv C c.K.M.n base t) c.K.E c.selected (FastNaf.point C Q 5 v j) := by
  have hl := FastNaf.magnitude_le (Or.inl rfl) v j
  have ho := (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hmag
  have ha : 1≤(FastNaf.magnitude 5 v j-1)/2+1 := by omega
  have hb : (FastNaf.magnitude 5 v j-1)/2+1≤8 := by omega
  have hi : (FastNaf.magnitude 5 v j-1)/2<8 := by omega
  have he : 2*((FastNaf.magnitude 5 v j-1)/2+1)-1=FastNaf.magnitude 5 v j := by omega
  have hd : ∀ x∈cachedSlots c.K.E c.selected,x∈jointSlots c := by intro x hx; jslots
  have hw : ∀ x∈cachedSlots c.K.E c.selected,x∈jointWork c := by intro x hx; jslots
  have hq : ∀ x∈cachedSlots (c.K.tblPt ((FastNaf.magnitude 5 v j-1)/2+1))
      (c.cache+64*((FastNaf.magnitude 5 v j-1)/2)),x∈jointLive c := by
    intro x hx
    apply jointStable_live c
    rcases List.mem_append.mp hx with hx|hx
    · exact jointStable_table c hL.layout.n ha (by omega) hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact jointStable_cache2 c hi
      · exact jointStable_cache3 c hi
  have hp : CachedPoint C (tmv C c.K.M.n base s)
      (c.K.tblPt ((FastNaf.magnitude 5 v j-1)/2+1)) (c.cache+64*((FastNaf.magnitude 5 v j-1)/2))
      (mul (FastNaf.magnitude 5 v j) Q) := by
    refine ⟨?_,h.stable.cache2 _ hi,h.stable.cache3 _ hi⟩
    have ht := h.stable.table _ ha hb
    rw [he] at ht
    exact ht
  refine WP.mono_syms (jointCachedFast_ok hL.layout.lay hL.layout.n hm h.field hmag h8
    hL.exy hL.exz hL.tableSmall hL.cacheSmall hL.tableBound hL.cacheBound hd hq
    hL.entryTable hL.entryCache hL.selectedCache hL.selectedEntry
    (by simp [jointLive,winRo]) h.stable.zero hL.zeroApart hp) fun t ⟨kt,it,pt⟩ st => ?_
  have kw := kt.mono hw
  exact ⟨kw,h.of_write hL.layout kt hw hd hL.accumApart
    (it.sub (fun _ hx => List.mem_append_right _ hx)) (hExternal s t kw st h.external),
    it.to_tmv,pt.to_tmv it (fun _ hx => List.mem_append_left _ hx)⟩

end VG.Proof.Weierstrass.X86_64
