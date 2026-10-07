import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem nafTable_initCounter_ok {s : State} {base : Addr} {tbl : Nat}
    (h20 : s.gpr .x20=off base tbl) :
    WP isa (.block [.addImm .x .x20 .x20 96,.movz .x .x19 7 0]) s fun t =>
      t.gpr .x20=off base (tbl+96) ∧ t.gpr .x19=7 ∧ Keeps [.x19,.x20] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    Size.bits,BitVec.setWidth_eq,show 96<4096 by decide,show 16*0<64 by decide,
    ite_true,ite_false,reduceCtorEq,h20,Option.some.injEq,exists_eq_left']
  refine ⟨?_,rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · simp only [off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem nafTable_init_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (ht : K.tbl<4096)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hp : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (.seq (fprogB K.M (dblJMul K.S K.P K.D)) (.block (copyPt 4 (Naf.twice K) K.D ++ copyPt 4 K.R K.P ++
      ([.addImm .x .x20 .x0 K.tbl] : List Instr) ++ Jacobian.tableStore K ++
      ([.addImm .x .x20 .x20 96,.movz .x .x19 7 0] : List Instr)))) s
      (fun t => NafTableInv K C base size P s t 1) := by
  have dr : ∀ x∈jacCoords K.D, x∈winOther K := by
    intro x hx; simp only [jacCoords,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have rr : ∀ x∈jacCoords K.R, x∈winOther K := by
    intro x hx; simp only [jacCoords,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have pr : ∀ x∈jacCoords K.P, x∈winRo K := by
    intro x hx; simp only [jacCoords,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have dw : ∀ x∈rcbW K.S K.D, x∈winOther K := fun _ hx => List.mem_append_right _ hx
  have slO : ∀ x∈winOther K, x∈jacWinSlots K := fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)
  have slR : ∀ x∈winRo K, x∈jacWinSlots K := fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)
  have bs := jacTblPt_mem K (a:=9) (by decide) (by decide)
  have bt : ∀ x∈jacCoords (Naf.twice K), x∈jacTblSlots K := by
    intro x hx; simp only [jacCoords,Naf.twice,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact jacTbl_mem K (a:=9) (c:=0) (by decide) (by decide) (by decide)
    · exact jacTbl_mem K (a:=9) (c:=1) (by decide) (by decide) (by decide)
    · exact jacTbl_mem K (a:=9) (c:=2) (by decide) (by decide) (by decide)
  have sepB : ∀ x∈winRo K ++ winOther K, ∀ y∈jacCoords (Naf.twice K), x≠y := by
    intro x hx y hy
    have hb := hL.tbl x hx
    simp only [jacCoords,Naf.twice,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hy
    omega
  have ds : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.P K.P, x∈jacWinSlots K := by
    intro x hx; rcases List.mem_append.mp hx with hx | hx
    · exact slO x (dw x hx)
    · apply slR
      simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have dv : ∀ x∈rcbR K.S K.P K.P, x∈winRo K := by
    intro x hx; simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have da : RcbApart K.S K.P K.P K.D := by
    refine ⟨(hL.rcbApart_RP hJ).nodup,?_⟩
    intro x hx hw; exact hL.ro x (dv x hx) (dw x hw)
  apply WP.seq
  refine WP.mono (jacDouble_ok hL.lay hAl hm hC ha da ds hI dv hP hp) fun a ⟨ka,ia,ja⟩ => ?_
  have ja : InvJ C (tmv C K.M.n base a K.D.x) (tmv C K.M.n base a K.D.y)
      (tmv C K.M.n base a K.D.z) (mul 2 P) := by
    have h := ia.point_tmv (fun _ hx => List.mem_append_left _ hx) ja
    rw [← mul_one_pt P,hC.add_mul_mul hP] at h
    simpa only [show 1+1=2 from rfl] using h
  have pa := ka.invJ hL.lay hI.scr (fun x hx => slO x (dw x hx))
    (fun x hx => slR x (pr x hx)) (fun x hx => hL.ro x (pr x hx) ∘ dw x) hp
  rw [List.append_assoc,List.append_assoc,List.append_assoc,WP.block_append_iff,←hL.n]
  refine WP.mono (copyPointFields_ok hL.lay hAl (q:=K.D) (o:=Naf.twice K)
    (by simp [jacCoords,Naf.twice,Jacobian.tablePt])
    (fun x hx y hy => sepB x (List.mem_append_right _ (dr x hx)) y hy) bs ia.to_tmv
    (fun _ hx => List.mem_append_left _ hx)) fun b ⟨eb,kb,ib,hb⟩ => ?_
  have jb : InvJ C (tmv C K.M.n base b (Naf.twice K).x) (tmv C K.M.n base b (Naf.twice K).y)
      (tmv C K.M.n base b (Naf.twice K).z) (mul 2 P) := by
    apply ib.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at hb
    rw [hb.1,hb.2.1,hb.2.2]; exact ja
  have pb := kb.invJ hL.lay ia.scr bs (fun x hx => slR x (pr x hx))
    (fun x hx hy => sepB x (List.mem_append_left _ (pr x hx)) x hy rfl) pa
  rw [WP.block_append_iff]
  refine WP.mono (copyPointFields_ok hL.lay hAl (q:=K.P) (o:=K.R)
    (by simp [jacCoords,hL.rxy,hL.rxz])
    (fun x hx y hy he => hL.ro x (pr x hx) (he ▸ rr y hy))
    (fun x hx => slO x (rr x hx)) ib.to_tmv
    (fun x hx => List.mem_append_right _ (List.mem_append_right _ (pr x hx)))) fun c ⟨ec,kc,ic,hc⟩ => ?_
  have jc : InvJ C (tmv C K.M.n base c K.R.x) (tmv C K.M.n base c K.R.y)
      (tmv C K.M.n base c K.R.z) P := by
    apply ic.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at hc
    rw [hc.1,hc.2.1,hc.2.2]; exact pb
  have bc := kc.invJ hL.lay ib.scr (fun x hx => slO x (rr x hx)) bs
    (fun x hx hy => sepB x (List.mem_append_right _ (rr x hy)) x hx rfl) jb
  rw [WP.block_append_iff]
  refine WP.mono (jacTree_pointer_ok (K:=K) ic.scr ht) fun d ⟨pd,kd⟩ => ?_
  have id := (ic.of_keeps kd (by decide)).to_tmv
  have jd : InvJ C (tmv C K.M.n base d K.R.x) (tmv C K.M.n base d K.R.y)
      (tmv C K.M.n base d K.R.z) P := by simpa only [tmv,kd.mem] using jc
  have bd : InvJ C (tmv C K.M.n base d (Naf.twice K).x) (tmv C K.M.n base d (Naf.twice K).y)
      (tmv C K.M.n base d (Naf.twice K).z) (mul 2 P) := by simpa only [tmv,kd.mem,Naf.twice] using bc
  have ts := jacTblPt_mem K (a:=1) (by decide) (by decide)
  have sep : K.R.x+96≤K.tbl+96*(1-1) ∨ K.tbl+96*(1-1)+96≤K.R.x := by
    have hx := hL.tbl K.R.x (List.mem_append_right _ (rr _ (by simp [jacCoords])))
    have hz := hL.tbl K.R.z (List.mem_append_right _ (rr _ (by simp [jacCoords])))
    rw [hL.rxz] at hz; omega
  rw [WP.block_append_iff]
  refine WP.mono (jacStorePoint_ok hL.lay hL.n hL.rxy hL.rxz id
    (by simpa using pd) (hAl.sl _ (slO _ (rr _ (by simp [jacCoords])))) ts
    (fun _ hx => List.mem_append_left _ hx) sep jd) fun e ⟨ke,ie,je⟩ => ?_
  have re := ke.invJ hL.lay id.scr ts (fun x hx => slO x (rr x hx)) (by
    intro x hx hx'
    have hs := hL.tbl x (List.mem_append_right _ (rr x hx))
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx'; omega) jd
  have be := ke.invJ hL.lay id.scr ts bs (by
    intro x hx hx'
    simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx hx'
    omega) bd
  have pe : e.gpr .x20=off base K.tbl := by rw [ke.gpr _ (by rw [hL.n]; decide),pd]
  refine WP.mono (nafTable_initCounter_ok pe) fun t ⟨pt,ct,kt⟩ => ?_
  have it := (ie.of_keeps kt (by decide)).to_tmv
  have ua := jacTree_progUnch ka (fun x hx => List.mem_append_left _ (dw x hx))
  have ub := jacTree_progUnch kb (fun x hx => List.mem_append_right _ (bt x hx))
  have uc := jacTree_progUnch kc (fun x hx => List.mem_append_left _ (rr x hx))
  have ue := jacTree_progUnch ke (by
    intro x hx; apply List.mem_append_right
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact jacTbl_mem K (a:=1) (c:=0) (by decide) (by decide) (by decide)
    · exact jacTbl_mem K (a:=1) (c:=1) (by decide) (by decide) (by decide)
    · exact jacTbl_mem K (a:=1) (c:=2) (by decide) (by decide) (by decide))
  have uw : Unch base (jacTreeWrites K) s.mem t.mem := by
    rw [kt.mem]; rw [kd.mem] at ue
    exact (ua.trans (ub.trans (uc.trans ue))).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw)
  refine ⟨it.sub ?_,?_,?_,?_,ct,by simpa using pt,?_,uw⟩
  · intro x hx
    simp only [nafTableLive,jacCoords,jacTreeSlots,Naf.twice,Jacobian.tablePt,List.range_succ,List.range_zero,
      List.map_append,List.map_cons,List.map_nil,List.nil_append,Nat.mul_one,Nat.sub_self,Nat.mul_zero,Nat.add_zero,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,show 32*2=64 from rfl] at hx ⊢
    grind
  · rw [show 2*1-1=1 from rfl,mul_one_pt]; simpa only [tmv,kt.mem] using re
  · simpa only [tmv,kt.mem,Naf.twice] using be
  · intro a ha ha1; obtain rfl : a=1 := by omega
    rw [show 2*1-1=1 from rfl,mul_one_pt]; simpa only [tmv,kt.mem] using je
  · have lift {W : List Nat} {u v : State} (k : ProgKeep K.M base W u v) : KeepRegs (jacTreeClob K) u v :=
      (KeepRegs.mono ⟨k.gpr,k.rd,k.wr,k.sp⟩ (fun _ hx => List.mem_append_left _ hx))
    have kdp := (Keeps.regs kd).mono (rs':=jacTreeClob K) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [jacTreeClob])
    have ktp := (Keeps.regs kt).mono (rs':=jacTreeClob K) (fun _ hx => List.mem_append_right _ hx)
    exact (lift ka).trans ((lift kb).trans ((lift kc).trans (kdp.trans ((lift ke).trans ktp))))

end VG.Proof.Weierstrass.AArch64
