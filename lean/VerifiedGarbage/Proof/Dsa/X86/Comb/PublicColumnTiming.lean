module

import VerifiedGarbage.Proof.Mont.X86.CombSquares

import VerifiedGarbage.Proof.Mont.X86.CombColumnControl

import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Proof.Mont.X86.CombColumns
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Dsa.X86.Comb
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.X86.Words
meta import VerifiedGarbage.Proof.Mont.X86.Words

/-! Column construction indexes only the public single-tooth entries. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (Columns)

def columnIndex : VG.X86.Taint.T := { regs := .ofList [.edi,.esi], flags := false }

theorem columnCopy_relCT (n tab src : Nat) :
    RelCT isa (VG.X86.Taint.Agree columnIndex) (VG.Impl.Mont.X86.Comb.copyToComb n tab src)
      (VG.X86.Taint.Agree columnIndex) := by
  exact erased_relCT _ (VG.Impl.Mont.X86.Comb.copyToComb 1 0 0)
    (VG.Taint.hintOf taint columnIndex (VG.Impl.Mont.X86.Comb.copyToComb 1 0 0))
    rfl rfl (by decide) (by taint_decide)

theorem columnSquares_check {n e : Nat} (h : Supported n e) :
    (VG.Taint.check taint (workspaceTaint false) (repeatSquares n 5 (rows e))
      (VG.Taint.hintOf taint (workspaceTaint false) (repeatSquares n 5 (rows e)))).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> taint_decide

theorem columnAdvance_relCT (base : Addr) (size i : Nat) (hz : 32≤size) (hi : i<4) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ w32 s.mem base 28=2^i ∧ w32 t.mem base 28=2^i)
      VG.Impl.Mont.X86.Comb.columnAdvance (VG.X86.Taint.Agree columnIndex) := by
  intro s t tr ur sf tf ⟨S,T,Hs,Ht⟩ E F
  have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
  have CT : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) VG.Impl.Mont.X86.Comb.columnAdvance
      (VG.X86.Taint.Agree (workspaceTaint false)) := checkedProgramChange (hint := .block []) rfl rfl
  obtain ⟨_,_,Is,Ks⟩ := wp_result (VG.Proof.Mont.X86.Comb.columnAdvance_ok S hz hi Hs) E
  obtain ⟨_,_,It,Kt⟩ := wp_result (VG.Proof.Mont.X86.Comb.columnAdvance_ok T hz hi Ht) F
  refine ⟨(CT _ _ _ _ _ _ A E F).1,agree_regs (rs := [.edi,.esi]) ?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · rw [Ks.1 _ (by decide),Kt.1 _ (by decide),DI]
  · exact Is.trans It.symm

theorem publicColumnStep_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g i : Nat)
    (hi : i<4) (s₀ t₀ : State) :
    RelCT isa (fun s t => Columns n (context n) (layout n e).size m g (rows e) i base s₀ s ∧
      Columns n (context n) (layout n e).size m g (rows e) i base t₀ t)
      (VG.Impl.Mont.X86.Comb.columnStep n (rows e) (context n+16*n))
      (VG.X86.Taint.Agree columnIndex) := by
  have hz : 32≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  unfold VG.Impl.Mont.X86.Comb.columnStep VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine RelCT.seq (R := fun (s t : State) => Scr s base (layout n e).size ∧ Scr t base (layout n e).size ∧
    w32 s.mem base 28=2^i ∧ w32 t.mem base 28=2^i) ?_
    (RelCT.seq (columnAdvance_relCT base _ i hz hi) (RelCT.seq (columnCopy_relCT _ _ _)
      (RelCT.seq (R := VG.X86.Taint.Agree columnIndex)
        (checkedProgramChange (hint := .block []) rfl rfl) (RelCT.block_nil (fun _ _ h => h)))))
  intro s t tr ur sf tf ⟨S,T⟩ Es Et
  obtain ⟨τ,check,le⟩ := Option.map_eq_some_iff.mp (columnSquares_check h)
  have CT := checkedProgramChange check le
  have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.ctx.scr.edi_toNat.trans T.ctx.scr.edi_toNat.symm)
  have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
  have advance {u v : State} {u₀ : State}
      (U : Columns n (context n) (layout n e).size m g (rows e) i base u₀ u)
      {trace} (E : Exec isa (repeatSquares n 5 (rows e)) u trace v) :
      Scr v base (layout n e).size ∧ w32 v.mem base 28=2^i := by
    obtain ⟨C,_,O,_⟩ := wp_result (combSquares_ok U.ctx (o := 5) (by decide) (by decide)
      (by decide) (by decide) (power_bounds h).1 (power_bounds h).2.1 U.value) E
    refine ⟨C.scr,?_⟩
    have H := O.val32 (d := 28) (k := 1) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> left <;> simp [slot,stride] <;> omega) (by decide)
    have equal : w32 v.mem base 28=w32 u.mem base 28 := by
      simpa only [val32,Nat.mul_zero,Nat.add_zero] using H
    exact equal.trans U.header
  obtain ⟨Cs,Hs⟩ := advance S Es
  obtain ⟨Ct,Ht⟩ := advance T Et
  exact ⟨(CT _ _ _ _ _ _ A Es Et).1,Cs,Ct,Hs,Ht⟩

theorem publicColumnLoop_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g : Nat) (s₀ t₀ : State) :
    RelCT isa (fun s t => Columns n (context n) (layout n e).size m g (rows e) 0 base s₀ s ∧
      Columns n (context n) (layout n e).size m g (rows e) 0 base t₀ t)
      (.loop (VG.Impl.Mont.X86.Comb.columnStep n (rows e) (context n+16*n)) .ne)
      (VG.X86.Taint.Agree columnIndex) := by
  let I (remaining : Nat) (s t : State) : Prop := ∃ i, remaining=4-i ∧ i<4 ∧
    Columns n (context n) (layout n e).size m g (rows e) i base s₀ s ∧
    Columns n (context n) (layout n e).size m g (rows e) i base t₀ t
  refine (RelCT.loop I ?_ 4).mono ?_ (fun _ _ h => h)
  · intro remaining s t tr ur sf tf ⟨i,eq,hi,S,T⟩ E F
    subst remaining
    obtain ⟨Trace,Agree⟩ := publicColumnStep_relCT h base m g i hi s₀ t₀ _ _ _ _ _ _ ⟨S,T⟩ E F
    obtain ⟨S',Zs⟩ := wp_result (VG.Proof.Mont.X86.Comb.columnStep_ok (table_layout h) S hi
      (power_bounds h).1 (power_bounds h).2.1) E
    obtain ⟨T',Zt⟩ := wp_result (VG.Proof.Mont.X86.Comb.columnStep_ok (table_layout h) T hi
      (power_bounds h).1 (power_bounds h).2.1) F
    refine ⟨Trace,?_,fun _ => Agree,?_⟩
    · change VG.X86.eval .ne sf=VG.X86.eval .ne tf
      simp only [VG.X86.eval,Zs,Zt]
    · intro hc
      have next : i+1<4 := by
        by_contra hn
        have eq : i+1=4 := by omega
        change VG.X86.eval .ne sf=some true at hc
        simp only [VG.X86.eval,Zs,eq,decide_true,Option.map_some,Bool.not_true] at hc
        cases hc
      exact ⟨4-(i+1),by omega,i+1,rfl,next,S',T'⟩
  · intro s t ⟨S,T⟩
    exact ⟨0,rfl,by decide,S,T⟩

structure PublicColumnsInput (n e m g : Nat) (base : Addr) (s : State) : Prop where
  ctx : Context n m base (layout n e).size s
  value : wordsVal s.mem base (slot n 5) n=VG.Proof.Mont.X86.Comb.columnValue n m g (rows e) 0
  entry : wordsVal s.mem base (context n+24*n) n=VG.Proof.Mont.X86.Comb.columnValue n m g (rows e) 0

theorem publicColumns_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g : Nat) :
    RelCT isa (fun s t => PublicColumnsInput n e m g base s ∧ PublicColumnsInput n e m g base t)
      (VG.Impl.Mont.X86.Comb.buildColumns n e (context n))
      (VG.X86.Taint.Agree columnIndex) := by
  unfold VG.Impl.Mont.X86.Comb.buildColumns
  let R := fun (s t : State) => ∃ s₀ t₀,
    Columns n (context n) (layout n e).size m g (rows e) 0 base s₀ s ∧
    Columns n (context n) (layout n e).size m g (rows e) 0 base t₀ t
  refine RelCT.seq (R := R) ?_ ?_
  · intro s t tr ur sf tf ⟨S,T⟩ Es Et
    have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.ctx.scr.edi_toNat.trans T.ctx.scr.edi_toNat.symm)
    have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
    have CT : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
        (.block [.mov .eax (VG.Impl.Mont.X86.Comb.imm 1), .store (sc 28) .eax])
        (VG.X86.Taint.Agree (workspaceTaint false)) := checkedProgramChange (hint := .block []) rfl rfl
    exact ⟨(CT _ _ _ _ _ _ A Es Et).1,s,t,
      wp_result (VG.Proof.Mont.X86.Comb.buildColumns_initial (table_layout h) S.ctx S.value S.entry) Es,
      wp_result (VG.Proof.Mont.X86.Comb.buildColumns_initial (table_layout h) T.ctx T.value T.entry) Et⟩
  · intro s t tr ur sf tf ⟨s₀,t₀,S,T⟩ Es Et
    exact publicColumnLoop_relCT h base m g s₀ t₀ _ _ _ _ _ _ ⟨S,T⟩ Es Et

end VG.Proof.Dsa.X86.Comb
