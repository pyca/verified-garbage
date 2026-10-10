import VerifiedGarbage.Proof.Weierstrass.X86.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86.RegFieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86.JacAddTiming

/-! ## `NafTableStoreTiming` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86

theorem nafTableStore_relCT {FM : Spec.Weierstrass.Mont.Modulus} {wk : Nat}
    {K : WinCfg} {base : Addr} {size j m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hW : WkOk FM K.M m size wk Sl) (hn : K.M.n=4)
    (hy : K.R.y=K.R.x+32) (hz : K.R.z=K.R.x+64)
    {V : List Nat} {E : Nat → Fin m} (hj : j<8) (hT : K.tbl+768≤size)
    (hD : ∀ x∈jacCoords (K.tblPt (j+1)),Sl x)
    (hQ : ∀ x∈jacCoords K.R,x∈V) (hSep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x)
    (hc : RegCT [.edi,.esi] (.block (Naf.tableStore K))) :
    RelCT isa (FieldPair K.M base size m Sl V E (BitVec.ofNat 32 j)) (.block (Naf.tableStore K))
      (FieldPair K.M base size m Sl (jacCoords (K.tblPt (j+1))++V)
        (pointTransferEnv E (K.tblPt (j+1)) K.R) (BitVec.ofNat 32 j)) := by
  have h := regFieldProgram_relCT (M:=K.M) (base:=base) (size:=size) (m:=m)
    (Sl:=Sl) (V:=V) (E:=E) (counter:=BitVec.ofNat 32 j) (counter':=BitVec.ofNat 32 j) (Pre:=fun _ => True) (Post:=fun _ => True) hc
    (fun s t hp _ _ => hp.pub.agree (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact hp.pub.edi
      · exact hp.count₁.trans hp.count₂.symm))
    (fun s hi ct _ => WP.mono (nafTableFields_ok hL hW hn hy hz hi hj ct hT hD hQ hSep)
      (fun t ⟨kt,it⟩ => ⟨Keeps.mono ⟨kt.gpr,kt.rd,kt.wr⟩ (by decide),it,
        (kt.gpr _ (by decide)).trans ct,trivial⟩))
  exact h.mono (fun _ _ hp => ⟨hp,trivial,trivial⟩) (fun _ _ hp => hp.1)

end VG.Proof.Weierstrass.X86

end

/-! ## `NafTableTimingInit` -/

section

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

end

/-! ## `NafTableTimingStep` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafTable_step_relCT {F : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : NafLay K size) (hW : WkOk F K.M C.p size wk (·∈nafSlots K)) (hJ : K.J=65) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hOne : K.one<C.p) (hm8 : m<8) (hc : NafTableChecks K F) :
    RelCT isa (NafTablePair K C base size m) (Naf.tableStep K F)
      (fun s t => NafTablePair K C base size (m+1) s t ∧
        s.cf=some (decide (m+1<8)) ∧ t.cf=some (decide (m+1<8))) := by
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := by
    intro x hx
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have sep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x := by
    have hx := hL.tbl K.R.x (by simp [winOther])
    have hz := hL.tbl K.R.z (by simp [winOther])
    rw [hL.rxz] at hz
    omega
  have slots : ∀ x∈rcbW K.S K.D++rcbR K.S K.R (Naf.twice K),x∈nafSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hx))
    · have he : x∈winRo K++winOther K ∨ x∈jacCoords (Naf.twice K) := by
        simp only [rcbR,winRo,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
        grind
      exact he.elim (List.mem_append_left _) (nafTblPt_mem K hL.n (by decide) (by decide) x)
  unfold NafTablePair
  apply RelCT.exists_
  intro E
  unfold Naf.tableStep
  have ac := jacAdd_relCT (counter:=BitVec.ofNat 32 m) (base:=base) (E:=E) hL.lay hW hm hc.add (hL.rcbApart_twice hJ)
    slots (nafTableLive_read K m) hOne
  apply RelCT.seq ac
  apply RelCT.exists_
  intro e
  rw [List.append_assoc,←hL.n]
  apply RelCT.block_append
  have cp := copyPoint_relCT (counter:=BitVec.ofNat 32 m) (base:=base) (E:=e) hL.lay hW rs
    (V:=jacCoords K.D++nafTableLive K m) (fun _ hx => List.mem_append_left _ hx) hc.copyStep
  apply RelCT.seq cp
  apply RelCT.block_append
  apply RelCT.seq (nafTableStore_relCT (base:=base) (j:=m) (E:=copyPointEnv e K.R K.D)
    hL.lay hW hL.n hL.rxy hL.rxz hm8 (by have := hL.table_le; omega)
    (nafTblPt_mem K hL.n (by omega) (by omega)) (fun _ hx => List.mem_append_left _ hx) sep hc.store)
  have adv := keepsField_relCT (counter:=BitVec.ofNat 32 m) (counter':=BitVec.ofNat 32 (m+1))
    (M:=K.M) (base:=base) (size:=size) (m:=C.p) (Sl:=(·∈nafSlots K))
    (V:=jacCoords (K.tblPt (m+1))++(jacCoords K.R++(jacCoords K.D++nafTableLive K m)))
    (E:=pointTransferEnv (copyPointEnv e K.R K.D) (K.tblPt (m+1)) K.R)
    (Pre:=fun _ => True) (Post:=fun s => s.cf=some (decide (m+1<8)))
    (ws:=[.esi]) (by decide) hc.advance
    (fun _ _ hp _ _ => hp.pub.agree (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact hp.count₁.trans hp.count₂.symm))
    (fun _ _ ct _ => WP.mono (nafTable_advance_ok hm8 ct) (fun _ ⟨ct,cf,hk⟩ => ⟨ct,cf,hk⟩))
  exact adv.mono (fun _ _ h => ⟨h,trivial,trivial⟩) (fun _ _ ⟨p,ps,pt⟩ =>
    ⟨⟨_,p.sub (by
      intro x hx
      simpa only [List.append_assoc] using nafTableLive_next K hL.n m x hx)⟩,ps,pt⟩)

end VG.Proof.Weierstrass.X86

end

/-! ## `NafTableTiming` -/

section

/-! Public table construction has equal traces for equal input field values. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafTable_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hW : WkOk F K.M C.p size wk (·∈nafSlots K)) (hJ : K.J=65) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hOne : K.one<C.p) (hc : NafTableChecks K F) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈nafSlots K) (winRo K) E counter)
      (Naf.table K F) (NafTablePair K C base size 8) := by
  let I := fun j s t => 1≤j ∧ j≤7 ∧ NafTablePair K C base size (8-j) s t
  have step : ∀ j, RelCT isa (I j) (Naf.tableStep K F) (fun s t =>
      eval .b s=eval .b t ∧
      (eval .b s=some false → NafTablePair K C base size 8 s t) ∧
      (eval .b s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj7 : j≤7
      · refine (nafTable_step_relCT hL hW hJ hm hOne (m:=8-j) (by omega) hc).mono
          (P':=I j) (fun _ _ h => h.2.2) ?_
        intro s t ⟨hp,cs,ct⟩
        refine ⟨cs.trans ct.symm,fun he => ?_,fun he => ?_⟩
        · change s.cf=some false at he
          have hn := of_decide_eq_false (Option.some.inj (cs.symm.trans he))
          have hj1 : j=1 := by omega
          subst j
          exact hp
        · change s.cf=some true at he
          have hy := of_decide_eq_true (Option.some.inj (cs.symm.trans he))
          refine ⟨j-1,by omega,by omega,by omega,?_⟩
          rw [show 8-(j-1)=8-j+1 from by omega]
          exact hp
      · exact RelCT.of_false (fun _ _ h => hj7 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  unfold Naf.table
  apply RelCT.assoc
  apply RelCT.seq (nafTable_init_relCT hL hW hm hc)
  exact (RelCT.loop I step 7).mono (fun _ _ hp => ⟨by decide,by decide,hp⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.X86

end
