module

public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZ
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafArith

/-! Build the odd peer table and its powers of Z without changing either digit stream. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem NafTableInv.readonly {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    {P : Point C} {s t : State} (hL : NafLay K size) (h : NafTableInv K C base size P s t m)
    {x : Nat} (hx : x∈winRo K) : tmv C K.M.n base t x=tmv C K.M.n base s x := by
  have hxs : x∈nafSlots K := List.mem_append_left _ (List.mem_append_left _ hx)
  unfold tmv
  rw [h.unch.wordsVal (fun w hw => ?_) (by
    have := hL.lay.le x hxs; have := h.field.scr.nowrap; omega_arith)]
  simp only [nafTableWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
  rcases hw with ⟨y,hy,rfl⟩|rfl
  · rcases List.mem_append.mp hy with hy|hy
    · exact hL.lay.apart x y hxs (List.mem_append_left _ (List.mem_append_right _ hy))
        (fun he => hL.ro x hx (he ▸ hy))
    · have hs := hL.tbl x (List.mem_append_left _ hx)
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hy
      have hi' := List.mem_range.mp hi
      have := entry_end_le (8*K.M.n) hi'
      dsimp only
      omega_arith
  · exact hL.lay.tmp x hxs

/-- The cache, in a loop or unrolled (`Joint.Cfg.cacheUnroll`). -/
theorem jointCache_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {a : State}
    (hL : JointInitLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (ii : Inv c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) (tmv C c.K.M.n base a) a) :
    WP isa (Joint.cacheCode c).inline a fun t =>
      CacheLoopKeep c.K.M base c.cache c.K.E.x a t ∧
      Inv c.K.M base size C.p (·∈jointSlots c) (cacheTableSlots c.K.M.n c.cache 8++nafTableLive c.K 8)
        (tmv C c.K.M.n base t) t ∧
      ∀ i<8,tmv C c.K.M.n base t (c.cache+16*c.K.M.n*i)=
          tmv C c.K.M.n base t (c.K.tbl+24*c.K.M.n*i+16*c.K.M.n)*
            tmv C c.K.M.n base t (c.K.tbl+24*c.K.M.n*i+16*c.K.M.n) ∧
        tmv C c.K.M.n base t (c.cache+16*c.K.M.n*i+8*c.K.M.n)=
          tmv C c.K.M.n base t (c.cache+16*c.K.M.n*i)*
            tmv C c.K.M.n base t (c.K.tbl+24*c.K.M.n*i+16*c.K.M.n) := by
  have hCL := hL.cacheLay
  rw [Joint.cacheCode]
  split
  · split
    · refine WP.mono (nafCacheUnrolled_current_ok hL.layout.n hL.layout.lay hm 8
        (by have := hCL.sep; omega_arith) ii hCL.hz hCL.cache) fun t ⟨kt,it,ht⟩ =>
        ⟨⟨⟨fun r hr => kt.gpr r (fun h => hr (List.mem_cons_of_mem _ h)),kt.rd,kt.wr⟩,
          kt.unch.mono fun w hw => ?_⟩,it,ht⟩
      simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
      rcases hw with ⟨x,hx,rfl⟩|rfl
      · exact Or.inl ⟨x,List.mem_append_left _ hx,rfl⟩
      · exact Or.inr rfl
    · exact nafCacheStaged_current_ok hL.layout.lay hm hCL ii
  · exact nafCacheTable_current_ok hL.layout.lay hm hCL ii

/-- The table `Naf.table` or its co-Z form builds gives what the joint loop needs. -/
theorem NafTableInv.post {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {Q : Point C}
    {s t : State} (hL : JointInitLayout c size) (ia : NafTableInv c.K C base size Q s t 8) :
    JointTablePost c C base size Q s t where
  field := ⟨ia.field.scr,ia.field.mod,fun x hx => List.mem_append_left _ (List.mem_append_left _
    (ia.field.sl x hx)),ia.field.lt,ia.field.val⟩
  keep := ia.keep.mono (by
    intro r hr
    simp only [nafTableClob,List.mem_append,List.mem_cons] at hr ⊢
    grind)
  unch := ia.unch.mono (by
    intro w hw
    simp only [nafTableWrites,jointInitRanges,jointInitWork,List.mem_append,List.mem_map,
      List.mem_singleton] at hw ⊢
    grind)
  ro _ hx := ia.readonly hL.naf hx
  table := ia.table

theorem jointTables_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {s : State}
    (hL : JointInitLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (hd : JDblOk C c.dbl) (hOne : c.K.one<C.p) (hQ : onCurve C Q=true)
    (hi : Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) (tmv C c.K.M.n base s) s)
    (hp : InvJ C (tmv C c.K.M.n base s c.K.P.x) (tmv C c.K.M.n base s c.K.P.y)
      (tmv C c.K.M.n base s c.K.P.z) Q) (h1 : tmv C c.K.M.n base s c.K.P.z=1)
    (hZ : c.coZ=true → PrimeOrder C ∧ 17≤C.n ∧ AM3 C)
    (hz : tmv C c.K.M.n base s c.K.zero=0)
    (hv : ∀ i<64*c.K.M.n+1,s.mem (off base (c.K.bits+i))=FastNaf.byte 5 v i)
    (hu : ∀ i<jointGLen c,s.mem (off base (c.gBits+i))=jointGByte c u i)
    (he : JointGenerator c C base T size row s) :
    WP isa (Code.seq (Joint.tableCode c) (Joint.cacheCode c)).inline s fun t =>
      JointLoopKeep c.K.M base (jointInitWork c) s t ∧
      Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) (tmv C c.K.M.n base t) t ∧
      JointStable c C base Q u v t ∧ JointGenerator c C base T size row t := by
  have tbl : WP isa (Joint.tableCode c).inline s (JointTablePost c C base size Q s) := by
    unfold Joint.tableCode
    split
    · next h =>
      obtain ⟨hO,hn,ha⟩ := hZ h
      exact WP.mono (nafTableCoZ_ok hL.naf hL.count hm hC hO hn ha hL.tableSmall hQ hi hp h1)
        fun t ht => ht.post hL
    · next h =>
      split
      · next C' hp' =>
        exact hL.tableCall (by simpa using h) C' hp' hm hC hd hOne hQ hi hp h1
      · exact WP.mono (nafTable_ok hL.naf hL.count hm hC hd hL.tableSmall hOne hQ hi hp)
          fun t ht => ht.post hL
  apply WP.seq
  refine WP.mono_syms tbl fun a ia sa => ?_
  have ii := ia.field
  have ka := ia.keep
  have ua := ia.unch
  have ea := he.keep_init hL.layout hi.mod.tmp ka ua sa
  have hCL := hL.cacheLay
  have hN := hL.naf
  have eo : ∀ x∈jacCoords c.K.E,x∈winOther c.K := by
    intro x hx
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  refine WP.mono_syms (jointCache_ok hL hm ii) fun t ⟨kt,it,ht⟩ st => ?_
  have ub : Unch base (jointInitRanges c) a.mem t.mem := kt.unch.mono (by
    intro w hw
    simp only [jointInitRanges,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
    rcases hw with ⟨x,hx,rfl⟩|rfl
    · refine Or.inl ⟨x,?_,rfl⟩
      simp only [cacheLoopSlots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hx|rfl|rfl|rfl
      · exact List.mem_append_left _ (List.mem_append_right _ (joint_cache_mem.mp hx))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (eo _ (by simp [jacCoords]))))
      · rw [← hN.exy]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (eo _ (by simp [jacCoords]))))
      · rw [← hN.exz]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (eo _ (by simp [jacCoords]))))
    · exact Or.inr rfl)
  have ut : Unch base (jointInitRanges c) s.mem t.mem := fun z hz => (ub z hz).trans (ua z hz)
  have kr : KeepRegs (.rbx::clob c.K.M.n) a t := kt.regs
  have notE : ∀ x,x∈cacheLoopSlots c.K.M.n c.cache c.K.E.x →
      x∈cacheTableSlots c.K.M.n c.cache 8 ∨ c.K.E.x≤x ∧ x+8*c.K.M.n≤c.K.E.x+24*c.K.M.n := by
    intro x hx
    simp only [cacheLoopSlots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|rfl|rfl|rfl
    · exact Or.inl hx
    all_goals exact Or.inr ⟨by omega_arith,by omega_arith⟩
  have tx := hN.tbl c.K.E.x (List.mem_append_right _ (eo _ (by simp [jacCoords])))
  have tz := hN.tbl c.K.E.z (List.mem_append_right _ (eo _ (by simp [jacCoords])))
  rw [hN.exz] at tz
  have iv : Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) (tmv C c.K.M.n base t) t :=
    it.sub (fun x hx => by
      rcases List.mem_append.mp hx with hx|hx
      · exact List.mem_append_right _ (joint_tableLive x hx)
      · exact List.mem_append_left _ (joint_cache_mem.mpr hx))
  have zero : tmv C c.K.M.n base t c.K.zero=0 := by
    unfold tmv
    rw [kt.unch.slot hL.layout.lay ii.scr hCL.slots (ii.sl _ (by simp [nafTableLive,winRo]))
      (fun hx => ?_)]
    · exact (ia.ro _ (by simp [winRo])).trans hz
    simp only [cacheLoopSlots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|hx|hx|hx
    · exact hL.zeroCache (joint_cache_mem.mp hx)
    · exact hN.ro c.K.zero (by simp [winRo]) (by rw [hx]; exact eo _ (by simp [jacCoords]))
    · exact hN.ro c.K.zero (by simp [winRo]) (by rw [hx,← hN.exy]; exact eo _ (by simp [jacCoords]))
    · exact hN.ro c.K.zero (by simp [winRo]) (by rw [hx,← hN.exz]; exact eo _ (by simp [jacCoords]))
  have table : ∀ n,1≤n → n≤8 → InvJ C (tmv C c.K.M.n base t (c.K.tblPt n).x)
      (tmv C c.K.M.n base t (c.K.tblPt n).y) (tmv C c.K.M.n base t (c.K.tblPt n).z) (mul (2*n-1) Q) := by
    intro n hn hn'
    apply kt.unch.invJ hL.layout.lay ii.scr hCL.slots
      (fun x hx => List.mem_append_left _ (List.mem_append_left _
        (nafTblPt_mem c.K hn (by omega_arith) x hx))) ?_ (ia.table n hn hn')
    intro x hx hc
    have hs := hL.cacheSep
    have := hL.layout.n
    have := entry_le (24*c.K.M.n) (show n-1≤7 by omega_arith)
    simp only [jacCoords,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases notE x hc with hc|hc
    · obtain ⟨i,hi,hx'⟩ := mem_cacheTableSlots.mp hc
      have := entry_end_le (16*c.K.M.n) hi
      omega_arith
    · omega_arith
  refine ⟨⟨ka.trans kr,ut⟩,iv,⟨zero,table,
    jointInit_digits hL (by have := hi.scr.nowrap; omega_arith) ut (by simp) hv,
    jointInit_digits hL (by have := hi.scr.nowrap; omega_arith) ut (by simp) hu,?_,?_⟩,
    ea.keep_init hL.layout ii.mod.tmp kr ub st⟩
  · intro i hi
    simpa only [WinCfg.tblPt,Nat.add_sub_cancel] using (ht i hi).1
  · intro i hi
    simpa only [WinCfg.tblPt,Nat.add_sub_cancel] using (ht i hi).2

end VG.Proof.Weierstrass.X86_64
