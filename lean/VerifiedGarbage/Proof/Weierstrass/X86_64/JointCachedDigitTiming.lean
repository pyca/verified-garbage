module

import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDigitTiming
public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheEntryFields
public import VerifiedGarbage.Proof.Weierstrass.X86_64.RegFieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacTiming
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheEntryPoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
public import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `Weierstrass.X86_64.NafCacheEntryTiming`, which only this module used -/

section

/-! A signed peer lookup has shared field results when its public digit agrees. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem nafSignedCachedEntry_relCT {K : WinCfg} {base : Addr} {size tbl dst m : Nat}
    [NeZero m] {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m}
    (hL : Lay K.M size Sl) (hn : K.M.n=4 ∨ K.M.n=6 ∨ K.M.n=9) (hm : UnitMod m (2^(64*K.M.n)))
    {b : BitVec 8}
    (ha : 1≤nafMagnitude b) (ha' : nafMagnitude b≤15) (hodd : nafMagnitude b%2=1)
    (hy : K.E.y=K.E.x+8*K.M.n) (hz : K.E.z=K.E.x+16*K.M.n)
    (hp : K.tbl<2^31) (hc : tbl<2^31)
    (hP : K.tbl+192*K.M.n≤size) (hC : tbl+128*K.M.n≤size)
    (hD : ∀ x∈cachedSlots K.M.n K.E dst,Sl x)
    (hQ : ∀ x∈cachedSlots K.M.n (K.tblPt ((nafMagnitude b-1)/2+1))
      (tbl+16*K.M.n*((nafMagnitude b-1)/2)),x∈V)
    (hEP : K.E.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.E.x)
    (hEC : K.E.x+24*K.M.n≤tbl ∨ tbl+128*K.M.n≤K.E.x)
    (hDC : dst+16*K.M.n≤tbl ∨ tbl+128*K.M.n≤dst)
    (hDE : dst+16*K.M.n≤K.E.x ∨ K.E.x+24*K.M.n≤dst)
    (hZero : K.zero∈V) (heZero : E K.zero=0) (hApart : K.zero∉cachedSlots K.M.n K.E dst)
    (hct : RegCT [.rdi,.r8] (Naf.signedCachedEntry K tbl dst)) :
    RelCT isa (fun s t => FieldPair K.M base size m Sl V E s t ∧
      s.gpr .r8=b.setWidth 64 ∧ t.gpr .r8=b.setWidth 64)
      (Naf.signedCachedEntry K tbl dst)
      (FieldPair K.M base size m Sl (cachedSlots K.M.n K.E dst++V) (cachedEntryEnv K E tbl dst b)) := by
  have h := regFieldProgram_relCT (M:=K.M) (base:=base) (size:=size) (m:=m)
    (Sl:=Sl) (V:=V) (E:=E) (Pre:=fun s => s.gpr .r8=b.setWidth 64)
    (Post:=fun _ => True) hct (fun s t p ds dt => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact p.1.scr.rdi.trans p.2.scr.rdi.symm
      · exact ds.trans dt.symm)) (fun s hi ds =>
        WP.mono (nafSignedCachedFields_ok hL hn hm hi ha ha' hodd ds hy hz hp hc hP hC
          hD hQ hEP hEC hDC hDE hZero heZero hApart) (fun _ ht => ⟨ht.2,trivial⟩))
  exact h.mono (fun _ _ ht => ht) (fun _ _ ht => ht.1)

end VG.Proof.Weierstrass.X86_64

end

end


/-! Timing of a peer digit with its precomputed Jacobian powers. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
                   List.not_mem_nil,or_false] at * <;> grind))

structure JointCachedChecks (c : Joint.Cfg) : Prop where
  read : RegCT [.rdi,.rbx] (.block (Naf.digitRead c.K))
  entry : RegCT [.rdi,.r8] (Naf.signedCachedEntry c.K c.cache c.selected)
  add : CachedJacChecks c.K c.K.R c.K.E c.K.D c.selected c.dbl
  copy : ScratchCT (.block (copyPt c.K.M.n c.K.R c.K.D))

theorem jointCachedSum_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (hc : JointCachedChecks c) (hds : JDblShape c.dbl)
    (h2 : E c.selected=E c.K.E.z*E c.K.E.z)
    (h3 : E (c.selected+8*c.K.M.n)=E c.selected*E c.K.E.z) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) (cachedSlots c.K.M.n c.K.E c.selected++jointLive c) E)
      (Joint.cachedAdd c).inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  refine jointAdd_relCT_dispatch (body := PointOps.addCachedBody c.K c.selected c.dbl) rfl (fun _ => rfl)
    (fun C' hp => (hL.calls.ok C' hp).1) ?_
  have sl : ∀ x∈(rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E)++[c.selected,c.selected+8*c.K.M.n],x∈jointSlots c := by intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E++[c.selected,c.selected+8*c.K.M.n],x∈cachedSlots c.K.M.n c.K.E c.selected++jointLive c := by intro x hx; jslots
  apply RelCT.seq (cachedJacAdd_relCT hL.lookup.layout.lay hm hc.add
    hL.addApart hL.cache2Apart hL.cache3Apart sl vr hOne h2 h3 hds)
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
    (hOne : c.K.one<C.p) (hj : j<64*c.K.M.n+1) (hc : JointCachedChecks c) (hds : JDblShape c.dbl)
    (hExternal : ∀ s t,VG.Proof.X25519.X86_64.Keeps [.r8] s t → t.syms=s.syms → External s → External t) :
    RelCT isa (fun s t => FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      JointCore c C base size Q u v External A s ∧ JointCore c C base size Q u v External A t ∧
      s.gpr .rbx=BitVec.ofNat 64 j ∧ t.gpr .rbx=BitVec.ofNat 64 j)
      (Joint.cachedDigit c).inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have hbytes : c.K.bits+j<size := by
    have hh := hL.lookup.layout.stableBounds (c.K.bits,64*c.K.M.n+1) (by simp [jointStableRanges])
    dsimp only at hh
    omega_arith
  apply nafDigitBranch_relCT hbytes hc.read (fun _ hs => hs.stable.peer j hj)
    (fun s t hk st hs => hs.of_keeps hk (by decide) (hExternal s t hk st hs.external))
  intro hb s t ts tt s' t' ⟨hp,cs,_,s8,t8⟩ es et
  have hmag : FastNaf.magnitude 5 v j≠0 := fun he => hb ((FastNaf.byte_zero_iff 5 v j).mpr he)
  have hmagn : nafMagnitude (FastNaf.byte 5 v j)=FastNaf.magnitude 5 v j := FastNaf.byte_magnitude 5 v j
  have ha : 1≤nafMagnitude (FastNaf.byte 5 v j) := by rw [hmagn]; omega_arith
  have hbound : nafMagnitude (FastNaf.byte 5 v j)≤15 := by
    rw [hmagn]; exact FastNaf.magnitude_le (Or.inl rfl) v j
  have ho : nafMagnitude (FastNaf.byte 5 v j)%2=1 := by
    rw [hmagn]; exact (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hmag
  let i := (nafMagnitude (FastNaf.byte 5 v j)-1)/2
  have hi : i<8 := by dsimp only [i]; omega_arith
  have hq : ∀ x∈cachedSlots c.K.M.n (c.K.tblPt (i+1)) (c.cache+16*c.K.M.n*i),x∈jointLive c := by
    intro x hx
    apply jointStable_live c
    rcases List.mem_append.mp hx with hx|hx
    · exact jointStable_table c (by omega_arith) (by omega_arith) hx
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
    exact ⟨cs.stable.table (i+1) (by omega_arith) (by omega_arith),cs.stable.cache2 i hi,cs.stable.cache3 i hi⟩
  have result := cachedEntryEnv_point (by have := hL.lookup.layout.n; omega_arith) hL.lookup.exy hL.lookup.exz hL.lookup.selectedEntry point
  have zero : E c.K.zero=0 := by
    rw [←hp.1.val _ (by simp [jointLive,winRo])]
    exact cs.stable.zero
  have ds : ∀ x∈cachedSlots c.K.M.n c.K.E c.selected,x∈jointSlots c := by intro x hx; jslots
  have entry := nafSignedCachedEntry_relCT (base:=base) (E:=E)
    hL.lookup.layout.lay hL.lookup.layout.n hm ha hbound ho hL.lookup.exy hL.lookup.exz
    hL.lookup.tableSmall hL.lookup.cacheSmall hL.lookup.tableBound hL.lookup.cacheBound ds hq
    hL.lookup.entryTable hL.lookup.entryCache hL.lookup.selectedCache hL.lookup.selectedEntry
    (by simp [jointLive,winRo]) zero hL.lookup.zeroApart hc.entry
  exact (RelCT.seq entry (jointCachedSum_relCT hL hm hOne hc hds result.2.1 result.2.2))
    _ _ _ _ _ _ ⟨hp,s8,t8⟩ es et

end VG.Proof.Weierstrass.X86_64
