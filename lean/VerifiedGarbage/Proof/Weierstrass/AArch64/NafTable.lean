import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ## `NafTableStep` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem nafTable_step_ok {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    (hm1 : 1≤m) (hm7 : m≤7) {s₀ s : State} (hI : NafTableInv K C base size P s₀ s m) :
    WP isa (Naf.tableStep K) s fun t => NafTableInv K C base size P s₀ t (m+1) := by
  have hf := hI.field
  have hv := nafTableLive_read K m
  have ds : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R (Naf.twice K), x∈jacWinSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hx))
    · have he : x∈winRo K ++ winOther K ∨ x∈jacCoords (Naf.twice K) := by
        simp only [rcbR,winRo,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
        grind
      rcases he with he | he
      · exact List.mem_append_left _ he
      · exact jacTblPt_mem K (by decide) (by decide) x he
  unfold Naf.tableStep
  apply WP.seq
  refine WP.mono (jacAdd_ok hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm hC ha (hL.rcbApart_twice hJ) ds hf hv hOne
    (hC.onCurve_mul hP _) (hC.onCurve_mul hP _) hI.point hI.twice) fun u ⟨eu,ka,iu,ju⟩ => ?_
  have jw : InvJ C (eu K.D.x) (eu K.D.y) (eu K.D.z) (mul (2*(m+1)-1) P) := by
    rw [hC.add_mul_mul hP,show 2*m-1+2=2*(m+1)-1 by omega] at ju
    exact ju
  have ka := ka.mono (W' := winOther K) (fun _ hx => List.mem_append_right _ hx)
  have pu : u.gpr .x20=off base (K.tbl+96*((m+1)-1)) := by
    rw [ka.gpr _ (by rw [hL.n]; decide),hI.pointer,Nat.add_sub_cancel]
  have vd : ∀ x∈rcbR K.S K.D K.D, x∈jacCoords K.D++nafTableLive K m := by
    intro x hx
    have hsa := hv K.S.a (by simp [rcbR])
    have hsb := hv K.S.b3 (by simp [rcbR])
    simp only [rcbR,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  rw [WP.block_append_iff]
  refine WP.mono (jacTreeCopyStore_ok hL hAl (by omega) (by omega) iu vd pu jw)
    fun v ⟨ks,iv,jr,jnew⟩ => ?_
  let W := winOther K ++ jacCoords (Jacobian.tablePt K (m+1))
  have kas : ProgKeep K.M base W s v := (ka.mono (fun _ hx => List.mem_append_left _ hx)).trans ks
  have p19 : v.gpr .x19=BitVec.ofNat 64 (8-m) := by
    rw [kas.gpr _ (by rw [hL.n]; decide),hI.counter]
  have p20 : v.gpr .x20=off base (K.tbl+96*m) := by
    rw [kas.gpr _ (by rw [hL.n]; decide),hI.pointer]
  refine WP.mono (nafAdvance_ok p19 p20 hm7) fun t ⟨hc,hp,kc⟩ => ?_
  have it := (iv.of_keeps kc (by decide)).to_tmv.sub (nafTableLive_next K hm1)
  have slots : ∀ x∈W, x∈jacWinSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ hx)
    · exact jacTblPt_mem K (by omega) (by omega) x hx
  have kct : KeepRegs (jacTreeClob K) v t := (Keeps.regs kc).mono (fun _ hx => List.mem_append_right _ hx)
  have kst : KeepRegs (jacTreeClob K) s t :=
    (KeepRegs.mono ⟨kas.gpr,kas.rd,kas.wr,kas.sp⟩ (fun _ hx => List.mem_append_left _ hx)).trans kct
  have uw : Unch base (jacTreeWrites K) s.mem t.mem := by
    rw [kc.mem]
    apply kas.unch.mono
    intro w hw
    simp only [jacTreeWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · refine Or.inl ⟨x,?_,rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · apply List.mem_append_right
        have hh := jacTblPt_mem K (by omega : 1≤m+1) (by omega : m+1≤16) x hx
        simp only [Jacobian.tablePt,jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact jacTbl_mem K (by omega) (by omega) (c:=0) (by decide)
        · exact jacTbl_mem K (by omega) (by omega) (c:=1) (by decide)
        · exact jacTbl_mem K (by omega) (by omega) (c:=2) (by decide)
    · exact Or.inr rfl
  have beq (x : Nat) (hx : x∈jacCoords (Naf.twice K)) : tmv C K.M.n base t x=tmv C K.M.n base s x := by
    unfold tmv; rw [kc.mem]
    rw [kas.slot hL.lay hf.scr slots (jacTblPt_mem K (by decide) (by decide) x hx) ?_]
    intro hw
    rcases List.mem_append.mp hw with hw | hw
    · have sep := hL.tbl x (List.mem_append_right _ hw)
      simp only [jacCoords,Naf.twice,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
      omega
    · simp only [jacCoords,Naf.twice,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx hw
      omega
  refine ⟨it,?_,?_,?_,hc,hp,hI.keep.trans kst,?_⟩
  · simpa only [tmv,kc.mem] using jr
  · rw [beq _ (by simp [jacCoords]),beq _ (by simp [jacCoords]),beq _ (by simp [jacCoords])]
    exact hI.twice
  · intro a ha1 ham
    by_cases he : a=m+1
    · subst a; simpa only [tmv,kc.mem] using jnew
    · have ham' : a≤m := by omega
      have teq (x : Nat) (hx : x∈jacCoords (Jacobian.tablePt K a)) :
          tmv C K.M.n base t x=tmv C K.M.n base s x := by
        unfold tmv; rw [kc.mem]
        rw [kas.slot hL.lay hf.scr slots (jacTblPt_mem K ha1 (by omega) x hx) ?_]
        intro hw
        rcases List.mem_append.mp hw with hw | hw
        · have sep := hL.tbl x (List.mem_append_right _ hw)
          simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
          omega
        · exact jacTable_ne ha1 ham' hx hw rfl
      rw [teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords])]
      exact hI.table a ha1 ham'
  · exact (hI.unch.trans uw).mono (fun _ hw => (List.mem_append.mp hw).elim id id)

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafTable` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- Build the eight odd multiples and the cached double. -/
theorem nafTable_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (ht : K.tbl<4096) (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    {s : State} (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (Naf.table K) s (fun t => NafTableInv K C base size P s t 8) := by
  unfold Naf.table
  apply WP.assoc
  refine WP.seq (WP.mono (nafTable_init_ok hL hJ hAl hm hC ha ht hP hI hJP) fun a ia => ?_)
  apply countLoop_ok (Inv := fun j t => NafTableInv K C base size P s t (8-j))
    (n := 7) (by decide)
  · intro j u hj hj7 hu
    refine WP.mono (nafTable_step_ok hL hJ hAl hm hC ha hOne hP (by omega) (by omega) hu)
      fun t it => ?_
    have he : 8-j+1=8-(j-1) := by omega
    refine ⟨he ▸ it,?_⟩
    have hc := it.counter
    have he' : 8-(8-j+1)=j-1 := by omega
    rwa [he'] at hc
  · intro t it; exact it
  · decide
  · exact ia

theorem nafTableLive_full (K : WinCfg) : ∀ x∈nafLive K, x∈nafTableLive K 8 := by
  intro x hx
  simp only [nafLive,List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx)))
  · simp only [nafTableLive,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    by_cases h : i<24
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩)
    · have hb : K.tbl+32*i ∈ jacCoords (Naf.twice K) := by
        simp only [jacCoords,Naf.twice,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false]
        omega
      exact List.mem_append_left _ (List.mem_append_right _ hb)

/-- Table construction preserves all 257 signed digits. -/
theorem NafTableInv.ready {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    {P : Point C} {β : Nat → BitVec 8} {s t : State} (hL : JacWinLay K size)
    (hI : NafTableInv K C base size P s t 8)
    (hz : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<257, s.mem (off base (K.bits+i))=β i) :
    Inv K.M base size C.p (·∈jacWinSlots K) (nafLive K) (tmv C K.M.n base t) t ∧
      NafStable K C base P β t := by
  refine ⟨hI.field.sub (nafTableLive_full K),?_,hI.table,?_⟩
  · rw [jacTree_ro_words hL hI.unch hI.field.scr.nowrap (by simp [winRo]),hz]
  · intro i hi
    rw [hI.unch.byte (fun w hw => ?_) (by have := hL.bits; have := hI.field.scr.nowrap; omega),hb i hi]
    simp only [jacTreeWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · have hb' := hL.bits_w x hx
      dsimp only; rw [hL.n]; omega
    · have hb' := hL.bits_tmp
      dsimp only; rw [hL.n]; omega

end VG.Proof.Weierstrass.AArch64

end
