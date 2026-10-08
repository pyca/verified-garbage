import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStoreTiming

/-! Fixed controls and equal field values through odd-table initialization. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

structure NafTableChecks (K : WinCfg) : Prop where
  double : ScratchCT (fprogB K.M (dblJMul K.S K.P (Naf.twice K))).inline
  copyFirst : ScratchCT (.block (copyPt K.M.n (K.tblPt 1) K.P))
  copyInit : ScratchCT (.block (copyPt K.M.n K.R K.P))
  initCounter : ScratchCT (.block [.mov32 .rbx (.imm 1)])
  add : JacAddChecks K K.R (Naf.twice K) K.D
  copyStep : ScratchCT (.block (copyPt K.M.n K.R K.D))
  store : RegCT [.rdi,.rbx] (.block (Naf.tableStore K))
  advance : RegCT [.rbx] (.block [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 8)])
  keepAdd : KeepReg.keeps .rbx (Jacobian.jacAdd K K.R (Naf.twice K) K.D).inline = true
  keepCopy : ∀ i∈instrs (.block (copyPt K.M.n K.R K.D) : Prog isa), Taint.clobbers i .rbx=false

def NafTablePair (K : WinCfg) (C : Curve) (base : Addr) (size m : Nat) (s t : State) : Prop :=
  ∃ E, FieldPair K.M base size C.p (·∈nafSlots K) (nafTableLive K m) E s t ∧
    s.gpr .rbx=BitVec.ofNat 64 m ∧ t.gpr .rbx=BitVec.ofNat 64 m

theorem nafTable_init_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hc : NafTableChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈nafSlots K) (winRo K) E)
      (Code.seq (fprogB K.M (dblJMul K.S K.P (Naf.twice K)))
        (.block (copyPt K.M.n (K.tblPt 1) K.P++copyPt K.M.n K.R K.P++([.mov32 .rbx (.imm 1)] : List Instr)))).inline
      (NafTablePair K C base size 1) := by
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := by
    intro x hx
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have pv : ∀ x∈jacCoords K.P,x∈winRo K := by
    intro x hx
    simp only [jacCoords,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have dv : ∀ x∈rcbR K.S K.P K.P,x∈winRo K := by
    intro x hx
    simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have ds : ∀ x∈rcbW K.S (Naf.twice K)++rcbR K.S K.P K.P,x∈nafSlots K := by
    intro x hx
    have he : x∈winRo K++winOther K ∨ x∈jacCoords (Naf.twice K) := by
      simp only [rcbW,rcbR,jacCoords,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    exact he.elim (List.mem_append_left _) (nafTblPt_mem K (by decide) (by decide) x)
  simp only [Code.inline]
  apply RelCT.seq (doubleFieldPlain_relCT hL.lay hm ds dv hc.double)
  rw [List.append_assoc]
  apply RelCT.block_append
  apply RelCT.seq (copyPoint_relCT hL.lay (nafTblPt_mem K (by decide) (by decide))
    (fun x hx => List.mem_append_right _ (pv x hx)) hc.copyFirst)
  apply RelCT.block_append
  apply RelCT.seq (copyPoint_relCT hL.lay rs
    (fun x hx => List.mem_append_right _ (List.mem_append_right _ (pv x hx))) hc.copyInit)
  have ctr := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈nafSlots K))
    (V:=jacCoords K.R++(jacCoords (K.tblPt 1)++(jacCoords (Naf.twice K)++winRo K)))
    (E:=copyPointEnv (copyPointEnv (runOps (dblJMul K.S K.P (Naf.twice K)) E) (K.tblPt 1) K.P) K.R K.P)
    (Pre:=fun _ => True) (Post:=fun s => s.gpr .rbx=1) (by decide : Reg.rdi∉[Reg.rbx])
    hc.initCounter (fun _ _ hp _ _ => fieldPair_public hp)
    (fun s _ _ => nafTable_initCounter_ok s)
  exact ctr.mono (fun _ _ hp => ⟨hp,trivial,trivial⟩) (fun _ _ ⟨hp,hs,ht⟩ => ⟨_,hp.sub (by
    intro x hx
    simp only [nafTableLive,jacCoords,nafTableSlots,Naf.twice,WinCfg.tblPt,List.range_succ,List.range_zero,
      List.map_append,List.map_cons,List.map_nil,List.nil_append,Nat.mul_one,Nat.sub_self,Nat.mul_zero,Nat.add_zero,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,show 8*K.M.n*2=16*K.M.n by omega] at hx ⊢
    grind),hs,ht⟩)

end VG.Proof.Weierstrass.X86_64
