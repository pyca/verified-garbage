import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableState

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
  refine WP.mono (jacAdd_ok hL.lay hAl hm hC ha (hL.rcbApart_twice hJ) ds hf hv hOne
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
