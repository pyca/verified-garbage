import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCopy

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

theorem nafTable_initCounter_ok (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 1)]) s fun t => t.gpr .rbx=1 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc32,State.setReg32,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨rfl,fun r hr => by simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_setReg,hr,ite_false],rfl,rfl,rfl⟩

theorem nafTable_init_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) {P : Point C} (hP : onCurve C P=true) {s : State}
    (hI : Inv K.M base size C.p (·∈nafSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hp : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) (tmv C K.M.n base s K.P.z) P) :
    WP isa (.seq (fprogB K.M (dblJMul K.S K.P (Naf.twice K)))
      (.block (copyPt K.M.n (K.tblPt 1) K.P++copyPt K.M.n K.R K.P++([.mov32 .rbx (.imm 1)] : List Instr)))) s
      (fun t => NafTableInv K C base size P s t 1) := by
  have rr : ∀ x∈jacCoords K.R,x∈winOther K := by
    intro x hx; simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have pr : ∀ x∈jacCoords K.P,x∈winRo K := by
    intro x hx; simp only [jacCoords,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have slO : ∀ x∈winOther K,x∈nafSlots K := fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)
  have slR : ∀ x∈winRo K,x∈nafSlots K := fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)
  have bs := nafTblPt_mem K (a:=9) (by decide) (by decide)
  have ts := nafTblPt_mem K (a:=1) (by decide) (by decide)
  have bt (a : Nat) (ha : 1≤a) (ha9 : a≤9) : ∀ x∈jacCoords (K.tblPt a),x∈nafTblSlots K := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · rw [tblPt_x]; exact nafTbl_slot K (by omega)
    · rw [tblPt_y]; exact nafTbl_slot K (by omega)
    · rw [tblPt_z]; exact nafTbl_slot K (by omega)
  have dv : ∀ x∈rcbR K.S K.P K.P,x∈winRo K := by
    intro x hx; simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have dw : ∀ x∈rcbW K.S (Naf.twice K),x∈nafWrites K := by
    intro x hx
    have he : x∈winOther K ∨ x∈jacCoords (Naf.twice K) := by
      simp only [rcbW,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
    exact he.elim (List.mem_append_left _) (fun h => List.mem_append_right _ (bt 9 (by decide) (by decide) x h))
  have ds : ∀ x∈rcbW K.S (Naf.twice K)++rcbR K.S K.P K.P,x∈nafSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have h := dw x hx
      simp only [nafWrites,nafSlots,List.mem_append] at h ⊢; grind
    · exact slR x (dv x hx)
  have da := hL.rcbApart_init hJ
  apply WP.seq
  refine WP.mono (jacDouble_ok hL.lay hm hC ha da ds hI dv hP hp) fun a ⟨ka,ia,ja⟩ => ?_
  have ja : InvJ C (tmv C K.M.n base a (Naf.twice K).x) (tmv C K.M.n base a (Naf.twice K).y)
      (tmv C K.M.n base a (Naf.twice K).z) (mul 2 P) := by
    have h := ia.point_tmv (fun _ hx => List.mem_append_left _ hx) ja
    rw [←mul_one_pt P,hC.add_mul_mul hP] at h
    simpa only [show 1+1=2 from rfl] using h
  have pa := ka.invJ hL.lay hI.scr (fun x hx => ds x (List.mem_append_left _ hx))
    (fun x hx => slR x (pr x hx)) (fun x hx => da.apart x (by
      simp only [jacCoords,rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)) hp
  have hn0 := hL.n
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyPointFields_ok hL.lay (q:=K.P) (o:=K.tblPt 1)
    (by simp [jacCoords,WinCfg.tblPt] <;> omega) (by
      intro x hx y hy he
      have hs := hL.tbl x (List.mem_append_left _ (pr x hx))
      simp only [jacCoords,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hy
      omega) ts ia.to_tmv (fun x hx => List.mem_append_right _ (pr x hx))) fun b ⟨eb,kb,ib,vb⟩ => ?_
  have jb : InvJ C (tmv C K.M.n base b (K.tblPt 1).x) (tmv C K.M.n base b (K.tblPt 1).y)
      (tmv C K.M.n base b (K.tblPt 1).z) P := by
    apply ib.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at vb
    rw [vb.1,vb.2.1,vb.2.2]; exact pa
  have pb := kb.invJ hL.lay ia.scr ts (fun x hx => slR x (pr x hx)) (by
    intro x hx hy
    have hs := hL.tbl x (List.mem_append_left _ (pr x hx))
    simp only [jacCoords,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hy; omega) pa
  have bb := kb.invJ hL.lay ia.scr ts bs (by
    intro x hx hy
    simp only [jacCoords,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hx hy; omega) ja
  rw [WP.block_append_iff]
  refine WP.mono (copyPointFields_ok hL.lay (q:=K.P) (o:=K.R)
    (by simp only [jacCoords,hL.rxy,hL.rxz,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,
      not_or,List.nodup_nil,not_false_eq_true,and_true]; omega)
    (fun x hx y hy he => hL.ro x (pr x hx) (he ▸ rr y hy))
    (fun x hx => slO x (rr x hx)) ib.to_tmv
    (fun x hx => List.mem_append_right _ (List.mem_append_right _ (pr x hx)))) fun c ⟨ec,kc,ic,vc⟩ => ?_
  have jc : InvJ C (tmv C K.M.n base c K.R.x) (tmv C K.M.n base c K.R.y) (tmv C K.M.n base c K.R.z) P := by
    apply ic.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at vc
    rw [vc.1,vc.2.1,vc.2.2]; exact pb
  have sep (a : Nat) (ha : 1≤a) (ha9 : a≤9) : ∀ x∈jacCoords (K.tblPt a),x∉jacCoords K.R := by
    intro x hx hy
    have hs := hL.tbl x (List.mem_append_right _ (rr x hy))
    simp only [jacCoords,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hx
    have := entry_end_le (24*K.M.n) (show a-1<9 by omega)
    omega
  have bc := kc.invJ hL.lay ib.scr (fun x hx => slO x (rr x hx)) bs (sep 9 (by decide) (by decide)) bb
  have tc := kc.invJ hL.lay ib.scr (fun x hx => slO x (rr x hx)) ts (sep 1 (by decide) (by decide)) jb
  refine WP.mono (nafTable_initCounter_ok c) fun t ⟨ct,kt⟩ => ?_
  have it := (ic.of_keeps kt (by decide)).to_tmv
  have ua := nafTable_progUnch ka dw
  have ub := nafTable_progUnch kb (fun x hx => List.mem_append_right _ (bt 1 (by decide) (by decide) x hx))
  have uc := nafTable_progUnch kc (fun x hx => List.mem_append_left _ (rr x hx))
  refine ⟨it.sub ?_,?_,?_,?_,ct,?_,?_⟩
  · intro x hx
    simp only [nafTableLive,jacCoords,nafTableSlots,Naf.twice,WinCfg.tblPt,List.range_succ,List.range_zero,
      List.map_append,List.map_cons,List.map_nil,List.nil_append,Nat.mul_one,Nat.sub_self,Nat.mul_zero,Nat.add_zero,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,show 8*K.M.n*2=16*K.M.n by omega] at hx ⊢
    grind
  · rw [show 2*1-1=1 from rfl,mul_one_pt]; simpa only [tmv,kt.2.1] using jc
  · simpa only [tmv,kt.2.1,Naf.twice] using bc
  · intro a ha ha1
    obtain rfl : a=1 := by omega
    rw [show 2*1-1=1 from rfl,mul_one_pt]; simpa only [tmv,kt.2.1] using tc
  · have lift {W : List Nat} {u v : State} (k : ProgKeep K.M base W u v) : KeepRegs (nafTableClob K) u v :=
      (KeepRegs.mono ⟨k.gpr,k.rd,k.wr⟩ (fun _ hx => List.mem_append_left _ hx))
    exact (lift ka).trans ((lift kb).trans ((lift kc).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (fun _ hx => List.mem_append_right _ hx))))
  · rw [kt.2.1]
    exact (ua.trans (ub.trans uc)).mono (by intro w hw; simpa only [List.mem_append,or_self] using hw)

end VG.Proof.Weierstrass.X86_64
