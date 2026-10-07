import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoadTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The public tree carries exact paired field values and fixed loop counters. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

structure NafTableChecks (K : WinCfg) : Prop where
  double : FieldCT (fprogB K.M (dblJMul K.S K.P K.D))
  copyTwice : FieldCT (.block (copyPt K.M.n (Naf.twice K) K.D))
  copyInit : FieldCT (.block (copyPt K.M.n K.R K.P))
  pointer : FieldCT (.block [.addImm .x .x20 .x0 K.tbl])
  store : RegCT [.x0,.x20] (.block (Jacobian.tableStore K))
  initCounter : RegCT [.x0,.x20] (.block [.addImm .x .x20 .x20 96,.movz .x .x19 7 0])
  add : JacAddChecks K K.R (Naf.twice K) K.D
  copyStep : FieldCT (.block (copyPt K.M.n K.R K.D))
  advance : RegCT [.x19,.x20] (.block [.addImm .x .x20 .x20 96,decCounter])
  keepAdd : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs (Jacobian.jacAdd K K.R (Naf.twice K) K.D), dstOf i≠some r

 theorem nafTable_init_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hJ : K.J=52) (hm : UnitMod C.p (2^(64*K.M.n))) (ht : K.tbl<4096) (hc : NafTableChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈jacWinSlots K) (winRo K) E)
      (.seq (fprogB K.M (dblJMul K.S K.P K.D)) (.block (copyPt 4 (Naf.twice K) K.D ++ copyPt 4 K.R K.P ++ [.addImm .x .x20 .x0 K.tbl] ++ Jacobian.tableStore K ++
        [.addImm .x .x20 .x20 96,.movz .x .x19 7 0])))
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (nafTableLive K 1) E' s t ∧
        s.gpr .x19=7 ∧ t.gpr .x19=7 ∧
        s.gpr .x20=off base (K.tbl+96) ∧ t.gpr .x20=off base (K.tbl+96)) := by
  have rs : ∀ x∈[K.R.x,K.R.y,K.R.z], x∈jacWinSlots K := by
    intro x hx; apply List.mem_append_left
    simp only [winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have rp : ∀ x∈[K.P.x,K.P.y,K.P.z], x∈winRo K := by
    intro x hx; simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have sep : K.R.x+96≤K.tbl ∨ K.tbl+96≤K.R.x := by
    have hx := hL.tbl K.R.x (by simp [winOther])
    have hz := hL.tbl K.R.z (by simp [winOther])
    rw [hL.rxz] at hz
    omega
  have ds : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.P K.P, x∈jacWinSlots K := by
    intro x hx; apply List.mem_append_left
    simp only [rcbW,rcbR,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have dv : ∀ x∈rcbR K.S K.P K.P, x∈winRo K := by
    intro x hx; simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have da : RcbApart K.S K.P K.P K.D := by
    refine ⟨(hL.rcbApart_RP hJ).nodup,?_⟩
    intro x hx hw; exact hL.ro x (dv x hx) (List.mem_append_right _ hw)
  have de := dblJChoice_eq true K.S K.P K.D
  have d := ofN_relCT (base:=base) (E:=E) hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm (dblJChoiceN_ok true)
    da ds dv (by rw [←de]; exact hc.double)
  rw [←de] at d
  apply RelCT.seq d
  rw [List.append_assoc,List.append_assoc,List.append_assoc,← hL.n]
  apply RelCT.block_append
  apply RelCT.seq (copyPoint_relCT hL.lay hAl (jacTblPt_mem K (a:=9) (by decide) (by decide))
    (fun _ hx => List.mem_append_left _ hx) hc.copyTwice)
  apply RelCT.block_append
  apply RelCT.seq (copyPoint_relCT hL.lay hAl rs (fun x hx => List.mem_append_right _ (List.mem_append_right _ (rp x hx))) hc.copyInit)
  apply RelCT.block_append
  have ptr := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jacWinSlots K)) (V:=[K.R.x,K.R.y,K.R.z]++(jacCoords (Naf.twice K)++([K.D.x,K.D.y,K.D.z]++winRo K))) (E:=copyPointEnv (copyPointEnv (runOps (dblJMul K.S K.P K.D) E) (Naf.twice K) K.D) K.R K.P)
    (Pre:=fun _ => True) (Post:=fun s => s.gpr .x20=off base K.tbl)
    (by decide : Reg.x0∉[Reg.x20]) hc.pointer
    (fun _ _ hp _ _ => hp.public) (fun s hi _ => jacTree_pointer_ok hi.scr ht)
  apply RelCT.seq (ptr.mono (fun _ _ hp => ⟨hp,trivial,trivial⟩) (fun _ _ hp => hp))
  apply RelCT.block_append
  have store := jacStore_relCT (base:=base) (V:=[K.R.x,K.R.y,K.R.z]++(jacCoords (Naf.twice K)++([K.D.x,K.D.y,K.D.z]++winRo K))) (a:=1) hL.lay hL.n hL.rxy hL.rxz (hAl.sl _ (rs _ (by simp)))
    (E:=copyPointEnv (copyPointEnv (runOps (dblJMul K.S K.P K.D) E) (Naf.twice K) K.D) K.R K.P) (jacTblPt_mem K (by decide) (by decide))
    (fun _ hx => List.mem_append_left _ hx) (by simpa using sep) hc.store
  have storeKeep := relCT_keepGpr (r:=.x20) (v:=off base K.tbl) store
    (tableStore_preserves K (by decide)) (by decide)
  apply RelCT.seq (storeKeep.mono
    (Q':=fun (s t : State) => ∃ e, FieldPair K.M base size C.p (·∈jacWinSlots K)
      (jacCoords (Jacobian.tablePt K 1)++([K.R.x,K.R.y,K.R.z]++(jacCoords (Naf.twice K)++([K.D.x,K.D.y,K.D.z]++winRo K)))) e s t ∧
      s.gpr .x20=off base K.tbl ∧ t.gpr .x20=off base K.tbl)
    (fun _ _ hp => ⟨hp,hp.2⟩) (fun _ _ ⟨⟨e,hp⟩,hs,ht⟩ => ⟨e,hp,hs,ht⟩))
  apply RelCT.exists_
  intro E'
  have ctr := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jacWinSlots K)) (V:=jacCoords (Jacobian.tablePt K 1)++([K.R.x,K.R.y,K.R.z]++(jacCoords (Naf.twice K)++([K.D.x,K.D.y,K.D.z]++winRo K)))) (E:=E')
    (Pre:=fun s => s.gpr .x20=off base K.tbl)
    (Post:=fun s => s.gpr .x20=off base (K.tbl+96) ∧ s.gpr .x19=7)
    (by decide : Reg.x0∉[Reg.x19,Reg.x20]) hc.initCounter
    (fun s t hp ps pt => ⟨hp.sp,fun r hr => by
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.trans pt.symm⟩)
    (fun s _ hp => WP.mono (nafTable_initCounter_ok hp) (fun _ ⟨hp,hc,hk⟩ => ⟨⟨hp,hc⟩,hk⟩))
  exact ctr.mono (fun _ _ hp => hp) (fun s t ⟨hp,hs,ht⟩ => ⟨E',hp.sub (by
    intro x hx
    simp only [nafTableLive,jacTreeSlots,jacCoords,Naf.twice,Jacobian.tablePt,
      List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,List.nil_append,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind),hs.2,ht.2,hs.1,ht.1⟩)


end VG.Proof.Weierstrass.AArch64
