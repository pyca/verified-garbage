module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInvariant
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheEntryPoint
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheEntryFields
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheNeg
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Mont.X86_64.Wide
public import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Impl.Ecdsa.X86_64
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86_64.MulPX
public import VerifiedGarbage.Proof.Mont.X86_64.OpsReg
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Proof.X25519.X86_64.Step
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! ### `Weierstrass.X86_64.JointCachedPoint`, which only this module used -/

section

/-! The cached peer lookup represents a nonzero width-five digit of the joint sum. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem jointCachedFast_ok {K : WinCfg} {s : State} {base : Addr} {size tbl dst u j : Nat}
    {C : Curve} {P : Point C}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hi : Inv K.M base size C.p Sl V E s)
    (hmag : FastNaf.magnitude 5 u j≠0)
    (h8 : s.gpr .r8=(FastNaf.byte 5 u j).setWidth 64)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((FastNaf.magnitude 5 u j-1)/2+1))
      (tbl+16*K.M.n*((FastNaf.magnitude 5 u j-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉cachedSlots K.M.n K.E dst)
    (hPoint : CachedPoint K.M.n C E (K.tblPt ((FastNaf.magnitude 5 u j-1)/2+1))
      (tbl+16*K.M.n*((FastNaf.magnitude 5 u j-1)/2)) (mul (FastNaf.magnitude 5 u j) P)) :
    WP isa (Naf.signedCachedEntry K tbl dst) s fun t =>
      ProgKeep K.M base (cachedSlots K.M.n K.E dst) s t ∧
      Inv K.M base size C.p Sl (cachedSlots K.M.n K.E dst++V)
        (cachedEntryEnv K E tbl dst (FastNaf.byte 5 u j)) t ∧
      CachedPoint K.M.n C (cachedEntryEnv K E tbl dst (FastNaf.byte 5 u j)) K.E dst
        (FastNaf.point C P 5 u j) := by
  have he : nafMagnitude (FastNaf.byte 5 u j)=FastNaf.magnitude 5 u j := FastNaf.byte_magnitude 5 u j
  have ha : 1≤nafMagnitude (FastNaf.byte 5 u j) := by rw [he]; omega_using [hmag]
  have ha' : nafMagnitude (FastNaf.byte 5 u j)≤15 := by
    rw [he]
    exact FastNaf.magnitude_le (Or.inl rfl) u j
  have hodd : nafMagnitude (FastNaf.byte 5 u j)%2=1 := by
    rw [he]
    exact (FastNaf.magnitude_odd_or_zero 5 u j).resolve_left hmag
  refine WP.mono (nafSignedCachedFields_ok hL hn hm hi ha ha' hodd h8 hy hz hp hc hP hC
    hD (by rw [he]; exact hQ) hEP hEC hDC hDE hZero heZero hApart) fun t ⟨kt,it⟩ => ?_
  have hpoint := cachedEntryEnv_point (E:=E) (b:=FastNaf.byte 5 u j) (by omega_using [hn]) hy hz hDE
    (by rw [he]; exact hPoint)
  have ep : (if (FastNaf.byte 5 u j).toNat<128 then mul (FastNaf.magnitude 5 u j) P
      else negPt (mul (FastNaf.magnitude 5 u j) P))=FastNaf.point C P 5 u j := by
    rw [FastNaf.point,←FastNaf.byte_negative 5 u j]
    by_cases h : (FastNaf.byte 5 u j).toNat<128
    · simp only [h,ite_true,show ¬128≤(FastNaf.byte 5 u j).toNat from by omega_using [h],decide_false,ite_false,Bool.false_eq_true]
    · simp only [h,ite_false,show 128≤(FastNaf.byte 5 u j).toNat from by omega_using [h],decide_true,ite_true]
  rw [ep] at hpoint
  exact ⟨kt,it,hpoint⟩

end VG.Proof.Weierstrass.X86_64

end

end


/-! Select a cached odd multiple while retaining the accumulator and both scalar streams. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
                   List.not_mem_nil,or_false] at * <;> grind))

structure JointLookupLayout (c : Joint.Cfg) (size : Nat) : Prop where
  layout : JointLayout c size
  exy : c.K.E.y=c.K.E.x+8*c.K.M.n
  exz : c.K.E.z=c.K.E.x+16*c.K.M.n
  tableSmall : c.K.tbl<2^31
  cacheSmall : c.cache<2^31
  tableBound : c.K.tbl+192*c.K.M.n≤size
  cacheBound : c.cache+128*c.K.M.n≤size
  entryTable : c.K.E.x+24*c.K.M.n≤c.K.tbl ∨ c.K.tbl+192*c.K.M.n≤c.K.E.x
  entryCache : c.K.E.x+24*c.K.M.n≤c.cache ∨ c.cache+128*c.K.M.n≤c.K.E.x
  selectedCache : c.selected+16*c.K.M.n≤c.cache ∨ c.cache+128*c.K.M.n≤c.selected
  selectedEntry : c.selected+16*c.K.M.n≤c.K.E.x ∨ c.K.E.x+24*c.K.M.n≤c.selected
  zeroApart : c.K.zero∉cachedSlots c.K.M.n c.K.E c.selected
  accumApart : ∀ x∈jacCoords c.K.R,x∉cachedSlots c.K.M.n c.K.E c.selected

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
        (cachedSlots c.K.M.n c.K.E c.selected++jointLive c) (tmv C c.K.M.n base t) t ∧
      CachedPoint c.K.M.n C (tmv C c.K.M.n base t) c.K.E c.selected (FastNaf.point C Q 5 v j) := by
  have hl := FastNaf.magnitude_le (Or.inl rfl) v j
  have ho := (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hmag
  have ha : 1≤(FastNaf.magnitude 5 v j-1)/2+1 := by omega_using []
  have hb : (FastNaf.magnitude 5 v j-1)/2+1≤8 := by omega_using [hl]
  have hi : (FastNaf.magnitude 5 v j-1)/2<8 := by omega_using [hl]
  have he : 2*((FastNaf.magnitude 5 v j-1)/2+1)-1=FastNaf.magnitude 5 v j := by omega_using [ho]
  have hd : ∀ x∈cachedSlots c.K.M.n c.K.E c.selected,x∈jointSlots c := by intro x hx; jslots
  have hw : ∀ x∈cachedSlots c.K.M.n c.K.E c.selected,x∈jointWork c := by intro x hx; jslots
  have hq : ∀ x∈cachedSlots c.K.M.n (c.K.tblPt ((FastNaf.magnitude 5 v j-1)/2+1))
      (c.cache+16*c.K.M.n*((FastNaf.magnitude 5 v j-1)/2)),x∈jointLive c := by
    intro x hx
    apply jointStable_live c
    rcases List.mem_append.mp hx with hx|hx
    · exact jointStable_table c ha (by omega_using [hl]) hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact jointStable_cache2 c hi
      · exact jointStable_cache3 c hi
  have hp : CachedPoint c.K.M.n C (tmv C c.K.M.n base s)
      (c.K.tblPt ((FastNaf.magnitude 5 v j-1)/2+1)) (c.cache+16*c.K.M.n*((FastNaf.magnitude 5 v j-1)/2))
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
