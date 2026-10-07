import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCopy

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

theorem nafTable_step_ok {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : NafLay K size) (hJ : K.J=65)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (ht : K.tbl<2^31) (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    (hm1 : 1≤m) (hm7 : m≤7) {s₀ s : State} (hI : NafTableInv K C base size P s₀ s m) :
    WP isa (Naf.tableStep K) s fun t => NafTableInv K C base size P s₀ t (m+1) ∧ t.cf=some (decide (m+1<8)) := by
  have hf := hI.field
  have hv := nafTableLive_read K m
  have ds : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R (Naf.twice K), x∈nafSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hx))
    · have he : x∈winRo K ++ winOther K ∨ x∈jacCoords (Naf.twice K) := by
        simp only [rcbR,winRo,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
        grind
      rcases he with he | he
      · exact List.mem_append_left _ he
      · exact nafTblPt_mem K hL.n (by decide) (by decide) x he
  unfold Naf.tableStep
  apply WP.seq
  refine WP.mono (jacAdd_ok hL.lay hm hC ha (hL.rcbApart_twice hJ) ds hf hv hOne
    (hC.onCurve_mul hP _) (hC.onCurve_mul hP _) hI.point hI.twice) fun u ⟨eu,ka,iu,ju⟩ => ?_
  have jw : InvJ C (eu K.D.x) (eu K.D.y) (eu K.D.z) (mul (2*(m+1)-1) P) := by
    rw [hC.add_mul_mul hP,show 2*m-1+2=2*(m+1)-1 by omega] at ju
    exact ju
  have ka := ka.mono (W' := winOther K) (fun _ hx => List.mem_append_right _ hx)
  have cm : u.gpr .rbx=BitVec.ofNat 64 m := by
    rw [ka.gpr _ (by rw [hL.n]; decide),hI.counter]
  rw [WP.block_append_iff]
  refine WP.mono (nafCopyStore_ok hL (by omega) ht iu
    (fun _ hx => List.mem_append_left _ hx) cm jw) fun v ⟨ks,iv,jr,jnew⟩ => ?_
  let W := winOther K ++ jacCoords (K.tblPt (m+1))
  have kas : ProgKeep K.M base W s v := (ka.mono (fun _ hx => List.mem_append_left _ hx)).trans (ks.mono (by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · apply List.mem_append_left
      simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    · exact List.mem_append_right _ hx))
  have cb : v.gpr .rbx=BitVec.ofNat 64 m := by
    rw [kas.gpr _ (by rw [hL.n]; decide),hI.counter]
  refine WP.mono (nafTable_advance_ok (by omega) cb) fun t ⟨hc,cf,kc⟩ => ?_
  have it := (iv.of_keeps kc (by decide)).to_tmv.sub (nafTableLive_next K hL.n m)
  have slots : ∀ x∈W, x∈nafSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ hx)
    · exact nafTblPt_mem K hL.n (by omega) (by omega) x hx
  have kct : KeepRegs (nafTableClob K) v t := (VG.Proof.Mont.X86_64.Keeps.regs kc).mono (fun _ hx => List.mem_append_right _ hx)
  have kst : KeepRegs (nafTableClob K) s t :=
    (KeepRegs.mono ⟨kas.gpr,kas.rd,kas.wr⟩ (fun _ hx => List.mem_append_left _ hx)).trans kct
  have uw : Unch base (nafTableWrites K) s.mem t.mem := by
    rw [kc.2.1]
    apply kas.unch.mono
    intro w hw
    simp only [nafTableWrites,nafWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · refine Or.inl ⟨x,?_,rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl hx
      · apply Or.inr
        simp only [WinCfg.tblPt,hL.n,jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact nafTbl_mem K (by omega) (by omega) (c:=0) (by decide)
        · exact nafTbl_mem K (by omega) (by omega) (c:=1) (by decide)
        · exact nafTbl_mem K (by omega) (by omega) (c:=2) (by decide)
    · exact Or.inr rfl
  have beq (x : Nat) (hx : x∈jacCoords (Naf.twice K)) : tmv C K.M.n base t x=tmv C K.M.n base s x := by
    unfold tmv; rw [kc.2.1]
    rw [kas.slot hL.lay hf.scr slots (nafTblPt_mem K hL.n (by decide) (by decide) x hx) ?_]
    intro hw
    rcases List.mem_append.mp hw with hw | hw
    · have sep := hL.tbl x (List.mem_append_right _ hw)
      simp only [jacCoords,Naf.twice,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx
      omega
    · simp only [jacCoords,Naf.twice,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx hw
      omega
  refine ⟨⟨it,?_,?_,?_,hc,hI.keep.trans kst,?_⟩,cf⟩
  · simpa only [tmv,kc.2.1] using jr
  · rw [beq _ (by simp [jacCoords]),beq _ (by simp [jacCoords]),beq _ (by simp [jacCoords])]
    exact hI.twice
  · intro a ha1 ham
    by_cases he : a=m+1
    · subst a; simpa only [tmv,kc.2.1] using jnew
    · have ham' : a≤m := by omega
      have teq (x : Nat) (hx : x∈jacCoords (K.tblPt a)) :
          tmv C K.M.n base t x=tmv C K.M.n base s x := by
        unfold tmv; rw [kc.2.1]
        rw [kas.slot hL.lay hf.scr slots (nafTblPt_mem K hL.n ha1 (by omega) x hx) ?_]
        intro hw
        rcases List.mem_append.mp hw with hw | hw
        · have sep := hL.tbl x (List.mem_append_right _ hw)
          simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx
          omega
        · simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx hw
          omega
      rw [teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords])]
      exact hI.table a ha1 ham'
  · exact (hI.unch.trans uw).mono (fun _ hw => (List.mem_append.mp hw).elim id id)

end VG.Proof.Weierstrass.X86_64
