module

public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZ
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableStoreTiming
import VerifiedGarbage.Proof.Weierstrass.CoZTable

/-! ### `Weierstrass.X86_64.NafTableCoZTiming`, which this module and modules that import it used -/

section

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
    omega_using [hz]
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
    (by have := hL.table_le; omega_using [this]) (nafTblPt_mem K (by omega_using []) (by omega_using [hm8]))
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
    have := hL.n; simp only [Naf.twice]; simp [jacCoords,WinCfg.tblPt] <;> omega_using [this]
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
      · refine (nafTableCoZ_step_relCT hL hJ hm ht (m:=8-j) (by omega_using [hj]) hc).mono
          (P':=I j) (fun _ _ h => h.2.2) ?_
        intro s t ⟨hp,cs,ct⟩
        refine ⟨cs.trans ct.symm,fun he => ?_,fun he => ?_⟩
        · change s.cf=some false at he
          have hn := of_decide_eq_false (Option.some.inj (cs.symm.trans he))
          have hj1 : j=1 := by omega_using [hj, hn]
          subst j
          exact hp
        · change s.cf=some true at he
          have hy := of_decide_eq_true (Option.some.inj (cs.symm.trans he))
          refine ⟨j-1,by omega_using [hj],by omega_using [hy],by omega_using [hj7],?_⟩
          rw [show 8-(j-1)=8-j+1 from by omega_using [hj, hj7]]
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

end

end

/-! ### `Weierstrass.X86_64.NafCacheBuildTiming`, which only this module used -/

section

/-! Exact cache environments relate the two public executions of table setup. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem nafCacheTable_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {ptbl tbl e : Nat}
    {V : List Nat} {E : Nat → Fin m} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    (hc : ScratchCT (Naf.cacheTable M ptbl tbl e).inline) :
    RelCT isa (FieldPair M base size m Sl V E) (Naf.cacheTable M ptbl tbl e).inline
      (FieldPair M base size m Sl (cacheTableSlots M.n tbl 8++V) (cacheTableEnv M.n ptbl tbl E 8)) :=
  fieldProgram_relCT hc (fun _ hi => WP.mono (nafCacheTable_fields_ok hL hm hC hi) fun _ h => h.2)

/-- `nafCacheTable_relCT`, for the loop's steps unrolled (`Naf.cacheStaged`). -/
theorem nafCacheStaged_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {ptbl tbl e : Nat}
    {V : List Nat} {E : Nat → Fin m} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    (hc : ScratchCT (Naf.cacheStaged M ptbl tbl e).inline) :
    RelCT isa (FieldPair M base size m Sl V E) (Naf.cacheStaged M ptbl tbl e).inline
      (FieldPair M base size m Sl (cacheTableSlots M.n tbl 8++V) (cacheTableEnv M.n ptbl tbl E 8)) :=
  fieldProgram_relCT hc (fun _ hi => WP.mono (nafCacheStaged_fields_ok hL hm hC hi) fun _ h => h.2)

/-! ## The cache unrolled -/

def cacheUnrolledEnv {m : Nat} [NeZero m] (n ptbl tbl : Nat) (E : Nat → Fin m) : Nat → Nat → Fin m
  | 0 => E
  | k+1 => runOps (Naf.cachePairOps n ptbl tbl k) (cacheUnrolledEnv n ptbl tbl E k)

theorem nafCacheUnrolled_fields_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) (k : Nat) {ptbl tbl : Nat}
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hZ : ∀ i<k,ptbl+24*M.n*i+16*M.n∈V)
    (hSl : ∀ i<k,Sl (tbl+16*M.n*i) ∧ Sl (tbl+16*M.n*i+8*M.n)) :
    WP isa (Naf.cacheUnrolled M ptbl tbl k).inline s fun t =>
      Inv M base size m Sl (cacheTableSlots M.n tbl k++V) (cacheUnrolledEnv M.n ptbl tbl E k) t := by
  induction k with
  | zero => exact WP.block_nil hI
  | succ k ih =>
    rw [Naf.cacheUnrolled]
    apply WP.seq
    refine WP.mono (ih (fun i hi => hZ i (by omega_using [hi])) (fun i hi => hSl i (by omega_using [hi]))) fun u iu => ?_
    refine WP.mono (nafCachePair_fields_ok hL hm iu
      (List.mem_append_right _ (hZ k (by omega_using []))) (hSl k (by omega_using [])).1 (hSl k (by omega_using [])).2)
      fun t ⟨_,it⟩ => it.sub ?_
    intro x hx
    simp only [cacheTableSlots,Naf.cachePairOps,validAfter,FOp.out,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind

theorem nafCacheUnrolled_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) (k : Nat) {ptbl tbl : Nat}
    {V : List Nat} {E : Nat → Fin m} (hZ : ∀ i<k,ptbl+24*M.n*i+16*M.n∈V)
    (hSl : ∀ i<k,Sl (tbl+16*M.n*i) ∧ Sl (tbl+16*M.n*i+8*M.n))
    (hc : ScratchCT (Naf.cacheUnrolled M ptbl tbl k).inline) :
    RelCT isa (FieldPair M base size m Sl V E) (Naf.cacheUnrolled M ptbl tbl k).inline
      (FieldPair M base size m Sl (cacheTableSlots M.n tbl k++V) (cacheUnrolledEnv M.n ptbl tbl E k)) :=
  fieldProgram_relCT hc (fun _ hi => nafCacheUnrolled_fields_ok hL hm k hi hZ hSl)

end VG.Proof.Weierstrass.X86_64

end

end


/-! Shared field values through odd-table setup, cache construction and the seed. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

/-- The table by calls of `C'`'s functions (`Joint.tableCall`) is constant
time, for any curve `C`: from states whose `P`, `a`, `3b` and zero agree to
states whose table's fields agree. -/
def JointTableCallCT (c : Joint.Cfg) (C' : Impl.Weierstrass.PointOps.Curve) : Prop :=
  ∀ {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}, JointInitLayout c size →
    UnitMod C.p (2^(64*c.K.M.n)) → c.K.one<C.p →
    RelCT isa (FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E)
      (Joint.tableCall c C').inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E' s t)

/-- The taint checks of the table: the co-Z table's (`Joint.Cfg.coZ`), the
table by calls' (`Joint.Cfg.pts`), or the other's. -/
def JointTableChecks (c : Joint.Cfg) : Prop :=
  if c.coZ then NafTableCoZChecks c.K else
  match c.pts with
  | some C' => JointTableCallCT c C'
  | none => NafTableChecks c.K c.dbl

theorem jointTables_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointInitLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (ht : JointTableChecks c) (hds : JDblShape c.dbl)
    (hc : ScratchCT (Joint.cacheCode c).inline) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E)
      (Code.seq (Joint.tableCode c) (Joint.cacheCode c)).inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have lift {E' : Nat → Fe C} {s : State}
      (hi : Inv c.K.M base size C.p (·∈nafSlots c.K) (nafTableLive c.K 8) E' s) :
      Inv c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E' s :=
    ⟨hi.scr,hi.mod,fun x hx => List.mem_append_left _ (List.mem_append_left _ (hi.sl x hx)),hi.lt,hi.val⟩
  have ofPair : ∀ s t, NafTablePair c.K C base size 8 s t →
      ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E' s t :=
    fun _ _ ⟨E',hp,_,_⟩ => ⟨E',lift hp.1,lift hp.2⟩
  have tbl : RelCT isa (FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E)
      (Joint.tableCode c).inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E' s t) := by
    by_cases h : c.coZ=true
    · simp only [Joint.tableCode,JointTableChecks,h,↓reduceIte] at ht ⊢
      exact (nafTableCoZ_relCT hL.naf hL.count hm hL.tableSmall ht).mono (fun _ _ h => h) ofPair
    · simp only [Joint.tableCode,JointTableChecks,h,↓reduceIte,Bool.false_eq_true] at ht ⊢
      rcases hp : c.pts with _ | C'
      · simp only [hp] at ht ⊢
        exact (nafTable_relCT hL.naf hL.count hm hL.tableSmall hOne ht hds).mono
          (fun _ _ h => h) ofPair
      · simp only [hp] at ht ⊢
        exact ht hL hm hOne
  apply RelCT.seq tbl
  have cache : ∀ E',RelCT isa
      (FieldPair c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E')
      (Joint.cacheCode c).inline
      (fun s t => ∃ E'',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E'' s t) := by
    intro E'
    have hCL := hL.cacheLay
    have code : RelCT isa
        (FieldPair c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E')
        (Joint.cacheCode c).inline
        (fun s t => ∃ E'',FieldPair c.K.M base size C.p (·∈jointSlots c)
          (cacheTableSlots c.K.M.n c.cache 8++nafTableLive c.K 8) E'' s t) := by
      revert hc
      rw [Joint.cacheCode]
      split
      · split
        · exact fun hc => (nafCacheUnrolled_relCT (E:=E') hL.layout.lay hm 8 hCL.hz hCL.cache hc).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
        · exact fun hc => (nafCacheStaged_relCT (E:=E') hL.layout.lay hm hCL hc).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
      · exact fun hc => (nafCacheTable_relCT (E:=E') hL.layout.lay hm hCL hc).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    exact code.mono
      (fun _ _ h => h) (fun _ _ ⟨_,h⟩ => ⟨_,h.sub (fun x hx => by
        rcases List.mem_append.mp hx with hx|hx
        · exact List.mem_append_right _ (joint_tableLive x hx)
        · exact List.mem_append_left _ (joint_cache_mem.mpr hx))⟩)
  exact RelCT.exists_ cache

theorem jointSeed_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointLayout c size) (hOne : c.K.one<C.p)
    (hc : ScratchCT (.block (Jacobian.infinity c.K c.K.R)))
    (ctr : ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top c)))])) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E)
      (.block (Jacobian.infinity c.K c.K.R++
        ([.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top c)))] : List Instr)))
      (FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c)
        (infinityEnv c.K.M C.p c.K.one E c.K.R)) := by
  have sl : ∀ x∈jacCoords c.K.R,x∈jointSlots c := by
    intro x hx
    simp only [jacCoords,jointSlots,nafSlots,winOther,rcbW,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  apply RelCT.block_append
  apply RelCT.seq (infinity_relCT hL.lay sl hOne hc)
  have step := keepsField_relCT (M:=c.K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jointSlots c)) (V:=jacCoords c.K.R++jointLive c)
    (E:=infinityEnv c.K.M C.p c.K.one E c.K.R) (Pre:=fun _ => True)
    (Post:=fun s => s.gpr .rbx=BitVec.ofNat 64 (Joint.top c)) (by decide : Reg.rdi∉[Reg.rbx]) ctr
    (fun _ _ hp _ _ => fieldPair_public hp) (fun s _ _ => jointCounter_ok s (by have := hL.n; have := joint_top_le c; omega_arith))
  exact step.mono (fun _ _ h => ⟨h,trivial,trivial⟩)
    (fun _ _ h => h.1.sub (fun _ hx => List.mem_append_right _ hx))

end VG.Proof.Weierstrass.X86_64
