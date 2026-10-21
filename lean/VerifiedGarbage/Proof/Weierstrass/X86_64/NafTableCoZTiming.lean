module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCoZField
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStoreTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The co-Z table has equal traces for equal input field values. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

/-- The taint checks of the co-Z table's pieces. -/
structure NafTableCoZChecks (K : WinCfg) : Prop where
  copyFirst : ScratchCT (.block (copyPt K.M.n (K.tblPt 1) K.P))
  initCounter : ScratchCT (.block [.mov32 .rbx (.imm 1)])
  dblu : ScratchCT (fprogB K.M (Naf.dbluOps K)).inline
  zaddu : ScratchCT (fprogB K.M (Naf.zadduOps K)).inline
  store : RegCT [.rdi,.rbx] (.block (Naf.tableStore K))
  advance : RegCT [.rbx] (.block [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 8)])
  twice : ScratchCT (.block (Naf.coZTwice K))

def CoZTablePair (K : WinCfg) (C : Curve) (base : Addr) (size m : Nat) (s t : State) : Prop :=
  ∃ E, FieldPair K.M base size C.p (·∈nafSlots K) (coZLive K m) E s t ∧
    s.gpr .rbx=BitVec.ofNat 64 m ∧ t.gpr .rbx=BitVec.ofNat 64 m

/-- A co-Z program keeps the counter and the environments equal. -/
theorem coZProg_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hm : UnitMod C.p (2^(64*K.M.n))) {σ : Nat → Nat} (hσ : CoZRen K σ)
    {N : List FOp} (hout : ∀ op∈N,op.out<11) {Rd : List Nat} (hR : readsOk N Rd=true)
    {V : List Nat} {E : Nat → Fe C} (hv : ∀ i∈Rd,σ i∈V)
    (hc : ScratchCT (fprogB K.M (N.map (CoZ.rename σ))).inline) {v : BitVec 64} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈nafSlots K) V E s t ∧
      s.gpr .rbx=v ∧ t.gpr .rbx=v) (fprogB K.M (N.map (CoZ.rename σ))).inline
      (fun s t => FieldPair K.M base size C.p (·∈nafSlots K) (validAfter (N.map (FOp.rename σ)) V)
        (runOps (N.map (FOp.rename σ)) E) s t ∧ s.gpr .rbx=v ∧ t.gpr .rbx=v) := by
  let F := fun u => Inv K.M base size C.p (·∈nafSlots K) (validAfter (N.map (FOp.rename σ)) V)
    (runOps (N.map (FOp.rename σ)) E) u ∧ u.gpr .rbx=v
  have h := ((scratch_relCT (M:=K.M) (base:=base) (size:=size) (Sl:=(·∈nafSlots K)) (V:=V) (E:=E) hc).mono
    (P':=fun (s t : State) => FieldPair K.M base size C.p (·∈nafSlots K) V E s t ∧ s.gpr .rbx=v ∧ t.gpr .rbx=v)
    (fun _ _ h => h.1) (fun _ _ h => h)).wp (F₁:=F) (F₂:=F) (fun s t ⟨p,hs,ht⟩ =>
      ⟨WP.mono (nafCoZ_ok hL hm hσ hout hR p.1 hv) fun _ ⟨k,i,_⟩ =>
        ⟨i,(k.gpr _ (rbx_not_clob _)).trans hs⟩,
       WP.mono (nafCoZ_ok hL hm hσ hout hR p.2 hv) fun _ ⟨k,i,_⟩ =>
        ⟨i,(k.gpr _ (rbx_not_clob _)).trans ht⟩⟩)
  exact h.mono (fun _ _ h => h) (fun _ _ ⟨_,⟨is,cs⟩,⟨it,ct⟩⟩ => ⟨⟨is,it⟩,cs,ct⟩)

theorem nafTableCoZ_init_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hc : NafTableCoZChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈nafSlots K) (winRo K) E)
      (Code.seq (.block (copyPt K.M.n (K.tblPt 1) K.P++([.mov32 .rbx (.imm 1)] : List Instr)))
        (fprogB K.M (Naf.dbluOps K))).inline
      (CoZTablePair K C base size 1) := by
  simp only [Code.inline]
  have ctr := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈nafSlots K)) (V:=jacCoords (K.tblPt 1)++winRo K)
    (E:=copyPointEnv E (K.tblPt 1) K.P)
    (Pre:=fun _ => True) (Post:=fun s => s.gpr .rbx=BitVec.ofNat 64 1) (by decide : Reg.rdi∉[Reg.rbx])
    hc.initCounter (fun _ _ hp _ _ => fieldPair_public hp)
    (fun s _ _ => nafTable_initCounter_ok s)
  refine RelCT.seq (R:=fun (s t : State) => FieldPair K.M base size C.p (·∈nafSlots K)
    (jacCoords (K.tblPt 1)++winRo K) (copyPointEnv E (K.tblPt 1) K.P) s t ∧
    s.gpr .rbx=BitVec.ofNat 64 1 ∧ t.gpr .rbx=BitVec.ofNat 64 1) ?_ ?_
  · apply RelCT.block_append
    apply RelCT.seq (copyPoint_relCT hL.lay (nafTblPt_mem K (by decide) (by decide))
      (fun x hx => coZ_P_ro K x hx) hc.copyFirst)
    exact ctr.mono (fun _ _ hp => ⟨hp,trivial,trivial⟩) (fun _ _ h => h)
  have hv : ∀ i∈[13,14,15],Naf.dbluσ K i∈jacCoords (K.tblPt 1)++winRo K := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> simp [Naf.dbluσ,winRo]
  exact (coZProg_relCT hL hm (nafDbluσ_ren (hL.toWinLay hJ)) CoZTable.dblu_out CoZTable.dblu_reads hv
    hc.dblu).mono (fun _ _ h => h) (fun _ _ ⟨p,hs,ht⟩ => ⟨_,p.sub (coZLive_dblu K),hs,ht⟩)

theorem nafTableCoZ_step_relCT {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : NafLay K size) (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4) (hm : UnitMod C.p (2^(64*K.M.n)))
    (ht : K.tbl<2^31) (hm8 : m<8) (hc : NafTableCoZChecks K) :
    RelCT isa (CoZTablePair K C base size m) (Naf.tableCoZStep K).inline
      (fun s t => CoZTablePair K C base size (m+1) s t ∧
        s.cf=some (decide (m+1<8)) ∧ t.cf=some (decide (m+1<8))) := by
  have sep : K.R.x+24*K.M.n≤K.tbl ∨ K.tbl+192*K.M.n≤K.R.x := by
    have hx := hL.tbl K.R.x (List.mem_append_right _ (coZ_R_other K _ (by simp [jacCoords])))
    have hz := hL.tbl K.R.z (List.mem_append_right _ (coZ_R_other K _ (by simp [jacCoords])))
    rw [hL.rxz] at hz
    omega
  have hv : ∀ i∈[0,1,8,9,10],Naf.coZσ K i∈coZLive K m := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp [Naf.coZσ,coZLive,jacCoords]
  unfold CoZTablePair
  apply RelCT.exists_
  intro E
  unfold Naf.tableCoZStep
  simp only [Code.inline]
  apply RelCT.seq (coZProg_relCT (E:=E) (v:=BitVec.ofNat 64 m) hL hm (nafCoZσ_ren (hL.toWinLay hJ))
    CoZTable.zaddu_out CoZTable.zaddu_reads hv hc.zaddu)
  apply RelCT.block_append
  apply RelCT.seq (nafTableStore_relCT (base:=base) (j:=m) hL.lay hL.n hL.rxy hL.rxz hm8 ht
    (by have := hL.table_le; omega) (nafTblPt_mem K (by omega) (by omega))
    (fun x hx => (mem_validAfter _ _).mpr (Or.inl (coZLive_R K m x hx))) sep hc.store)
  have adv := keepsField_relCT (M:=K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈nafSlots K))
    (V:=jacCoords (K.tblPt (m+1))++validAfter (CoZ.zaddu.map (FOp.rename (Naf.coZσ K))) (coZLive K m))
    (E:=pointTransferEnv (runOps (CoZ.zaddu.map (FOp.rename (Naf.coZσ K))) E) (K.tblPt (m+1)) K.R)
    (Pre:=fun s => s.gpr .rbx=BitVec.ofNat 64 m)
    (Post:=fun s => s.gpr .rbx=BitVec.ofNat 64 (m+1) ∧ s.cf=some (decide (m+1<8)))
    (by decide : Reg.rdi∉[Reg.rbx]) hc.advance
    (fun _ _ _ ps pt => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ps.trans pt.symm))
    (fun _ _ hp => WP.mono (nafTable_advance_ok hm8 hp) (fun _ ⟨ct,cf,hk⟩ => ⟨⟨ct,cf⟩,hk⟩))
  exact adv.mono (fun _ _ h => h) (fun _ _ ⟨p,ps,pt⟩ =>
    ⟨⟨_,p.sub (fun x hx => by
      rcases List.mem_append.mp (coZLive_next K m x hx) with h|h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ ((mem_validAfter _ _).mpr (Or.inl h))),ps.1,pt.1⟩,ps.2,pt.2⟩)

theorem nafTableCoZ_twice_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hc : NafTableCoZChecks K) :
    RelCT isa (CoZTablePair K C base size 8) (.block (Naf.coZTwice K)) (NafTablePair K C base size 8) := by
  unfold CoZTablePair
  apply RelCT.exists_
  intro E
  have tS := nafTblPt_mem K (a:=9) (by decide) (by decide)
  have tn := coZ_tbl_other hL (a:=9) (by decide) (by decide)
  have hN : (jacCoords (Naf.twice K)).Nodup := by
    have := hL.n; simp only [Naf.twice]; simp [jacCoords,WinCfg.tblPt] <;> omega
  have hqa : ∀ x∈jacCoords (Naf.coZD K),∀ y∈jacCoords (Naf.twice K),x≠y :=
    fun x hx y hy he => tn y hy (he ▸ coZ_D_other K x hx)
  let F := fun u : State => u.gpr .rbx=BitVec.ofNat 64 8
  have cp := ((copyPoint_relCT (base:=base) (E:=E) (V:=coZLive K 8) hL.lay tS (coZLive_D K 8)
    hc.twice).mono (P':=fun (s t : State) => FieldPair K.M base size C.p (·∈nafSlots K) (coZLive K 8) E s t ∧
      s.gpr .rbx=BitVec.ofNat 64 8 ∧ t.gpr .rbx=BitVec.ofNat 64 8)
    (fun _ _ h => h.1) (fun _ _ h => h)).wp (F₁:=F) (F₂:=F) (fun s t ⟨p,hs,ht⟩ =>
      ⟨WP.mono (copyPointFields_ok hL.lay hN hqa tS p.1 (coZLive_D K 8)) fun _ ⟨_,k,_⟩ =>
        (k.gpr _ (rbx_not_clob _)).trans hs,
       WP.mono (copyPointFields_ok hL.lay hN hqa tS p.2 (coZLive_D K 8)) fun _ ⟨_,k,_⟩ =>
        (k.gpr _ (rbx_not_clob _)).trans ht⟩)
  exact cp.mono (fun _ _ h => h) (fun _ _ ⟨p,cs,ct⟩ => ⟨_,p.sub (coZLive_twice K),cs,ct⟩)

theorem nafTableCoZ_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hJ : 1≤K.J ∧ 4*K.J≤64*K.M.n+4) (hm : UnitMod C.p (2^(64*K.M.n)))
    (ht : K.tbl<2^31) (hc : NafTableCoZChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (·∈nafSlots K) (winRo K) E)
      (Naf.tableCoZ K).inline (NafTablePair K C base size 8) := by
  let I := fun j s t => 1≤j ∧ j≤7 ∧ CoZTablePair K C base size (8-j) s t
  have step : ∀ j, RelCT isa (I j) (Naf.tableCoZStep K).inline (fun s t =>
      eval .b s=eval .b t ∧
      (eval .b s=some false → CoZTablePair K C base size 8 s t) ∧
      (eval .b s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj7 : j≤7
      · refine (nafTableCoZ_step_relCT hL hJ hm ht (m:=8-j) (by omega) hc).mono
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
  unfold Naf.tableCoZ
  simp only [Code.inline]
  apply RelCT.assoc
  apply RelCT.seq (nafTableCoZ_init_relCT hL hJ hm hc)
  apply RelCT.seq ((RelCT.loop I step 7).mono (fun _ _ hp => ⟨by decide,by decide,hp⟩) (fun _ _ h => h))
  exact nafTableCoZ_twice_relCT hL hc

end VG.Proof.Weierstrass.X86_64
