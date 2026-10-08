import VerifiedGarbage.Proof.Weierstrass.X86.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableStoreTiming

/-! Fixed controls and equal field values through odd-table initialization. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

structure NafTableChecks (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prop where
  double : ScratchCT (fprog F (dblJMul K.S K.P (Naf.twice K)))
  copyFirst : ScratchCT (.block (copyPt K.M.n (K.tblPt 1) K.P))
  copyInit : ScratchCT (.block (copyPt K.M.n K.R K.P))
  initCounter : ScratchCT (.block [.mov .esi (.imm 1)])
  add : JacAddChecks K F K.R (Naf.twice K) K.D
  copyStep : ScratchCT (.block (copyPt K.M.n K.R K.D))
  store : RegCT [.edi,.esi] (.block (Naf.tableStore K))
  advance : RegCT [.esi] (.block [.alu .add .esi (.imm 1),.alu .cmp .esi (.imm 8)])

def NafTablePair (K : WinCfg) (C : Curve) (base : Addr) (size m : Nat) (s t : State) : Prop :=
  ∃ E, FieldPair K.M base size C.p (·∈nafSlots K) (nafTableLive K m) E (BitVec.ofNat 32 m) s t

theorem nafTable_init_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hW : WkOk F K.M C.p size wk (·∈nafSlots K)) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hc : NafTableChecks K F) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈nafSlots K) (winRo K) E counter)
      (.seq (fprog F (dblJMul K.S K.P (Naf.twice K)))
        (.block (copyPt 4 (K.tblPt 1) K.P++copyPt 4 K.R K.P++([.mov .esi (.imm 1)] : List Instr))))
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
    exact he.elim (List.mem_append_left _) (nafTblPt_mem K hL.n (by decide) (by decide) x)
  apply RelCT.seq (doubleFieldPlain_relCT hL.lay hW hm ds dv hc.double)
  rw [List.append_assoc,←hL.n]
  apply RelCT.block_append
  apply RelCT.seq (copyPoint_relCT hL.lay hW (nafTblPt_mem K hL.n (by decide) (by decide))
    (fun x hx => List.mem_append_right _ (pv x hx)) hc.copyFirst)
  apply RelCT.block_append
  apply RelCT.seq (copyPoint_relCT hL.lay hW rs
    (fun x hx => List.mem_append_right _ (List.mem_append_right _ (pv x hx))) hc.copyInit)
  have ctr := keepsField_relCT (counter:=counter) (counter':=1)
    (M:=K.M) (base:=base) (size:=size) (m:=C.p) (Sl:=(·∈nafSlots K))
    (V:=jacCoords K.R++(jacCoords (K.tblPt 1)++(jacCoords (Naf.twice K)++winRo K)))
    (E:=copyPointEnv (copyPointEnv (runOps (dblJMul K.S K.P (Naf.twice K)) E) (K.tblPt 1) K.P) K.R K.P)
    (Pre:=fun _ => True) (Post:=fun _ => True) (ws:=[.esi]) (by decide)
    hc.initCounter (fun _ _ hp _ _ => hp.pub.agree (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact hp.pub.edi
      · exact hp.pub.esp))
    (fun s _ _ _ => WP.mono (nafTable_initCounter_ok s) (fun _ ⟨ct,kt⟩ => ⟨ct,trivial,kt⟩))
  exact ctr.mono (fun _ _ hp => ⟨hp,trivial,trivial⟩) (fun _ _ ⟨hp,_,_⟩ => ⟨_,hp.sub (by
    intro x hx
    simp only [nafTableLive,jacCoords,nafTableSlots,Naf.twice,WinCfg.tblPt,hL.n,List.range_succ,List.range_zero,
      List.map_append,List.map_cons,List.map_nil,List.nil_append,Nat.mul_one,Nat.sub_self,Nat.mul_zero,Nat.add_zero,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,show 32*2=64 from rfl] at hx ⊢
    grind)⟩)

end VG.Proof.Weierstrass.X86
