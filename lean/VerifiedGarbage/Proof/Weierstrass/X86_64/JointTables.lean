import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoop

/-! Build the odd peer table and its powers of Z without changing either digit stream. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem NafTableInv.readonly {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    {P : Point C} {s t : State} (hL : NafLay K size) (h : NafTableInv K C base size P s t m)
    {x : Nat} (hx : x∈winRo K) : tmv C K.M.n base t x=tmv C K.M.n base s x := by
  have hxs : x∈nafSlots K := List.mem_append_left _ (List.mem_append_left _ hx)
  unfold tmv
  rw [h.unch.wordsVal (fun w hw => ?_) (by
    have := hL.lay.le x hxs; have := h.field.scr.nowrap; omega)]
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
      omega
  · exact hL.lay.tmp x hxs

theorem jointTables_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G} {s : State}
    (hL : JointInitLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : c.K.one<C.p) (hQ : onCurve C Q=true)
    (hi : Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) (tmv C c.K.M.n base s) s)
    (hp : InvJ C (tmv C c.K.M.n base s c.K.P.x) (tmv C c.K.M.n base s c.K.P.y)
      (tmv C c.K.M.n base s c.K.P.z) Q)
    (hz : tmv C c.K.M.n base s c.K.zero=0)
    (hv : ∀ i<64*c.K.M.n+1,s.mem (off base (c.K.bits+i))=FastNaf.byte 5 v i)
    (hu : ∀ i<64*c.K.M.n+1,s.mem (off base (c.gBits+i))=FastNaf.byte 7 u i)
    (he : JointGenerator c C base T size row s) :
    WP isa (Code.seq (Naf.table c.K) (Naf.cacheTable c.K.M c.K.tbl c.cache 8)).inline s fun t =>
      JointLoopKeep c.K.M base (jointInitWork c) s t ∧
      Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) (tmv C c.K.M.n base t) t ∧
      JointStable c C base Q u v t ∧ JointGenerator c C base T size row t := by
  apply WP.seq
  refine WP.mono_syms (nafTable_ok hL.naf hL.count hm hC ha hL.tableSmall hOne hQ hi hp)
    fun a ia sa => ?_
  have ii : Inv c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) (tmv C c.K.M.n base a) a :=
    ⟨ia.field.scr,ia.field.mod,fun x hx => List.mem_append_left _ (List.mem_append_left _ (ia.field.sl x hx)),
      ia.field.lt,ia.field.val⟩
  have hcsl : ∀ x∈cacheTableSlots c.K.M.n c.cache 8,x∈jointSlots c := fun _ hx =>
    List.mem_append_right _ (joint_cache_mem.mp hx)
  have hZ : ∀ i<8,c.K.tbl+24*c.K.M.n*i+16*c.K.M.n∈nafTableLive c.K 8 := by
    intro i hi
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨3*i+2,List.mem_range.mpr (by omega),
      by rw [slot_three_mul_two,Nat.add_assoc]⟩
  have csl : ∀ i<8,(c.cache+16*c.K.M.n*i∈jointSlots c) ∧
      (c.cache+16*c.K.M.n*i+8*c.K.M.n∈jointSlots c) := by
    intro i hi
    exact ⟨hcsl _ (mem_cacheTableSlots.mpr ⟨i,hi,Or.inl rfl⟩),
      hcsl _ (mem_cacheTableSlots.mpr ⟨i,hi,Or.inr rfl⟩)⟩
  have ka : KeepRegs (.rbx::clob c.K.M.n) s a := ia.keep.mono (by
    intro r hr
    simp only [nafTableClob,List.mem_append,List.mem_cons] at hr ⊢
    grind)
  have ua : Unch base (jointInitRanges c) s.mem a.mem := ia.unch.mono (by
    intro w hw
    simp only [nafTableWrites,jointInitRanges,jointInitWork,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
    grind)
  have ea := he.keep_init hL.layout hi.mod.tmp ka ua sa
  refine WP.mono_syms (nafCacheTable_current_ok hL.layout.n hL.layout.lay hm 8
    (by have := hL.cacheSep; omega) ii hZ csl) fun t ⟨kt,it,ht⟩ st => ?_
  have ub : Unch base (jointInitRanges c) a.mem t.mem := kt.unch.mono (by
    intro w hw
    simp only [jointInitRanges,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
    rcases hw with ⟨x,hx,rfl⟩|rfl
    · exact Or.inl ⟨x,List.mem_append_right _ (joint_cache_mem.mp hx),rfl⟩
    · exact Or.inr rfl)
  have ut : Unch base (jointInitRanges c) s.mem t.mem := fun z hz => (ub z hz).trans (ua z hz)
  have kr : KeepRegs (.rbx::clob c.K.M.n) a t :=
    (⟨kt.gpr,kt.rd,kt.wr⟩ : KeepRegs (clob c.K.M.n) a t).mono (fun _ hr => List.mem_cons_of_mem _ hr)
  have iv : Inv c.K.M base size C.p (·∈jointSlots c) (jointLive c) (tmv C c.K.M.n base t) t :=
    it.sub (fun x hx => by
      rcases List.mem_append.mp hx with hx|hx
      · exact List.mem_append_right _ (joint_tableLive x hx)
      · exact List.mem_append_left _ (joint_cache_mem.mpr hx))
  have zero : tmv C c.K.M.n base t c.K.zero=0 := by
    unfold tmv
    rw [kt.slot hL.layout.lay ii.scr hcsl (ii.sl _ (by simp [nafTableLive,winRo]))
      (fun hx => hL.zeroCache (joint_cache_mem.mp hx))]
    exact (ia.readonly hL.naf (by simp [winRo])).trans hz
  have table : ∀ n,1≤n → n≤8 → InvJ C (tmv C c.K.M.n base t (c.K.tblPt n).x)
      (tmv C c.K.M.n base t (c.K.tblPt n).y) (tmv C c.K.M.n base t (c.K.tblPt n).z) (mul (2*n-1) Q) := by
    intro n hn hn'
    apply kt.invJ hL.layout.lay ii.scr hcsl
      (fun x hx => List.mem_append_left _ (List.mem_append_left _
        (nafTblPt_mem c.K hn (by omega) x hx))) ?_ (ia.table n hn hn')
    intro x hx hc
    obtain ⟨i,hi,hx'⟩ := mem_cacheTableSlots.mp hc
    have hs := hL.cacheSep
    have := hL.layout.n
    have := entry_end_le (16*c.K.M.n) hi
    have := entry_le (24*c.K.M.n) (show n-1≤7 by omega)
    simp only [jacCoords,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hx
    omega
  refine ⟨⟨ka.trans kr,ut⟩,iv,⟨zero,table,
    jointInit_digits hL (by have := hi.scr.nowrap; omega) ut (by simp) hv,
    jointInit_digits hL (by have := hi.scr.nowrap; omega) ut (by simp) hu,?_,?_⟩,
    ea.keep_init hL.layout ii.mod.tmp kr ub st⟩
  · intro i hi
    simpa only [WinCfg.tblPt,Nat.add_sub_cancel] using (ht i hi).1
  · intro i hi
    simpa only [WinCfg.tblPt,Nat.add_sub_cancel] using (ht i hi).2

end VG.Proof.Weierstrass.X86_64
