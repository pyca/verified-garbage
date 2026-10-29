module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicColumnTiming
public import VerifiedGarbage.Proof.Mont.X86.CombSubsets

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSelectTiming
import VerifiedGarbage.Proof.Mont.X86.CombSubsetControl
import VerifiedGarbage.Proof.Mont.X86.CombAccess
import Init.Prelude
import VerifiedGarbage.Impl.Mont.X86.CombTable
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rsa.FixedBaseCombSubset
/-! The subset construction loop has exactly 31 public iterations. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/PublicSubsetAccessTiming.lean`, which only this module imported.
section

/-! The subset builder preserves its public indices across each table lookup. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure SubsetIndex (base : Addr) (size a lo idx : Nat) (s : State) : Prop where
  scr : Scr s base size
  count : s.gpr .esi=BitVec.ofNat 32 a
  low : w32 s.mem base 28=lo
  index : w32 s.mem base 4=idx

theorem subsetIndex_agree {base : Addr} {size a lo idx : Nat} {s t : State}
    (S : SubsetIndex base size a lo idx s) (T : SubsetIndex base size a lo idx t) :
    VG.X86.Taint.Agree columnIndex s t := by
  apply agree_regs (rs := [.edi,.esi])
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
  · exact S.count.trans T.count.symm

theorem subsetSelect_relCT {n e : Nat} (h : Supported n e) (base : Addr) (a lo idx o : Nat)
    (hi : idx<32) (ho : o=5 ∨ o=6) :
    RelCT isa (fun s t => SubsetIndex base (layout n e).size a lo idx s ∧ SubsetIndex base (layout n e).size a lo idx t)
      (VG.Impl.Mont.X86.Comb.publicSelect n (context n+16*n) (slot n o))
      (fun s t => SubsetIndex base (layout n e).size a lo idx s ∧ SubsetIndex base (layout n e).size a lo idx t) := by
  have L := table_layout h
  have shape : 32≤slot n o ∧ slot n o+8*n≤context n ∧ slot n o+8*n≤(layout n e).size ∧ 32≤(layout n e).size := by
    rcases ho with rfl|rfl <;>
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have step {s : State} (S : SubsetIndex base (layout n e).size a lo idx s) :
      WP isa (VG.Impl.Mont.X86.Comb.publicSelect n (context n+16*n) (slot n o)) s
        (SubsetIndex base (layout n e).size a lo idx) := by
    have ent := L.entry hi
    refine WP.mono (VG.Proof.Mont.X86.Comb.publicSelect_ok S.scr L.positive (by omega)
      (by rw [S.index]; exact Nat.le_trans ent.2 L.bound) shape.2.2.1 (.inl (by unfold entry; omega))) fun t ⟨O,_,K⟩ => ?_
    exact ⟨S.scr.of_keeps K (by decide),(K.1 .esi (by decide)).trans S.count,
      (O.w32 (by omega) (by decide)).trans S.low,(O.w32 (by omega) (by decide)).trans S.index⟩
  intro s t tr ur sf tf ⟨S,T⟩ E F
  have CT := publicSelect_relCT base (layout n e).size n (context n+16*n) (slot n o) (by omega)
  exact ⟨(CT _ _ _ _ _ _ ⟨S.scr,T.scr,S.index.trans T.index.symm⟩ E F).1,
    wp_result (step S) E,wp_result (step T) F⟩

theorem subsetLow_relCT (base : Addr) (size a lo idx : Nat) (hz : 32≤size) :
    RelCT isa (fun s t => SubsetIndex base size a lo idx s ∧ SubsetIndex base size a lo idx t)
      VG.Impl.Mont.X86.Comb.subsetLow
      (fun s t => SubsetIndex base size a lo lo s ∧ SubsetIndex base size a lo lo t) := by
  have CT : RelCT isa (VG.X86.Taint.Agree columnIndex) VG.Impl.Mont.X86.Comb.subsetLow
      (VG.X86.Taint.Agree columnIndex) := checkedProgramChange (hint := .block []) rfl rfl
  have step {s : State} (S : SubsetIndex base size a lo idx s) :
      WP isa VG.Impl.Mont.X86.Comb.subsetLow s (SubsetIndex base size a lo lo) := by
    refine WP.mono (VG.Proof.Mont.X86.Comb.subsetLow_ok S.scr hz) fun t ⟨O,V,K⟩ => ?_
    exact ⟨S.scr.of_keeps K (by decide),(K.1 .esi (by decide)).trans S.count,
      (O.w32 (by decide) (by decide)).trans S.low,V.trans S.low⟩
  intro s t tr ur sf tf ⟨S,T⟩ E F
  exact ⟨(CT _ _ _ _ _ _ (subsetIndex_agree S T) E F).1,wp_result (step S) E,wp_result (step T) F⟩

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/PublicSubsetTiming.lean`, which only this module imported.
section

/-! Subset completion uses a public counter for both direct table accesses. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (Subsets)
open VG.Proof.Rsa.FixedBaseComb (lowTooth)

theorem subsetIndices_relCT (base : Addr) (size a : Nat) (hz : 32≤size) (ha : a<32) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.gpr .esi=BitVec.ofNat 32 a ∧ t.gpr .esi=BitVec.ofNat 32 a)
      VG.Impl.Mont.X86.Comb.subsetIndices
      (fun s t => SubsetIndex base size a (lowTooth a) (a-lowTooth a) s ∧
        SubsetIndex base size a (lowTooth a) (a-lowTooth a) t) := by
  have CT : RelCT isa (VG.X86.Taint.Agree columnIndex) VG.Impl.Mont.X86.Comb.subsetIndices
      (VG.X86.Taint.Agree columnIndex) := checkedProgramChange (hint := .block []) rfl rfl
  intro s t tr ur sf tf ⟨S,T,Is,It⟩ E F
  have A : VG.X86.Taint.Agree columnIndex s t := by
    apply agree_regs (rs := [.edi,.esi])
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
    · exact Is.trans It.symm
  obtain ⟨_,Hs,Ws,Ks⟩ := wp_result (VG.Proof.Mont.X86.Comb.subsetIndices_ok S hz ha Is) E
  obtain ⟨_,Ht,Wt,Kt⟩ := wp_result (VG.Proof.Mont.X86.Comb.subsetIndices_ok T hz ha It) F
  exact ⟨(CT _ _ _ _ _ _ A E F).1,
    ⟨S.of_keeps Ks (by decide),(Ks.1 .esi (by decide)).trans Is,Hs,Ws⟩,
    ⟨T.of_keeps Kt (by decide),(Kt.1 .esi (by decide)).trans It,Ht,Wt⟩⟩

theorem publicSubsetStep_relCT {n e : Nat} (h : Supported n e) (base : Addr) (a : Nat)
    (ha : 0<a) (ha32 : a<32) :
    RelCT isa (fun s t => Scr s base (layout n e).size ∧ Scr t base (layout n e).size ∧
        s.gpr .esi=BitVec.ofNat 32 a ∧ t.gpr .esi=BitVec.ofNat 32 a)
      (VG.Impl.Mont.X86.Comb.subsetStep n (context n+16*n))
      (VG.X86.Taint.Agree columnIndex) := by
  have hz : 32≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  obtain ⟨_,loLe,remLt,_⟩ := VG.Proof.Rsa.FixedBaseComb.lowTooth_bounds a ha32 ha
  unfold VG.Impl.Mont.X86.Comb.subsetStep VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine RelCT.seq (subsetIndices_relCT base _ a hz ha32)
    (RelCT.seq (subsetSelect_relCT h base a _ _ 6 (by omega) (.inr rfl))
      (RelCT.seq (subsetLow_relCT base _ a _ _ hz) (RelCT.seq
        ((subsetSelect_relCT h base a _ _ 5 (by omega) (.inl rfl)).mono (fun _ _ p => p)
          (fun _ _ p => subsetIndex_agree p.1 p.2))
        (RelCT.seq (R := VG.X86.Taint.Agree columnIndex) ?_
          (RelCT.seq (columnCopy_relCT _ _ _) (RelCT.seq (R := VG.X86.Taint.Agree columnIndex) ?_
            (RelCT.block_nil (fun _ _ h => h))))))))
  · exact checkedProgramChange (mul_check true _ _ _ _ _ _) rfl
  · exact checkedProgramChange (hint := .block []) rfl rfl

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (Subsets TableAt knownSubset)

theorem publicSubsetLoop_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g : Nat) (s₀ t₀ : State) :
    RelCT isa (fun s t => Subsets n (context n) (layout n e).size m g (32*e) 1 base s₀ s ∧
      Subsets n (context n) (layout n e).size m g (32*e) 1 base t₀ t)
      (.loop (VG.Impl.Mont.X86.Comb.subsetStep n (context n+16*n)) .ne)
      (VG.X86.Taint.Agree columnIndex) := by
  let I (remaining : Nat) (s t : State) : Prop := ∃ a, remaining=32-a ∧ 0<a ∧ a<32 ∧
    Subsets n (context n) (layout n e).size m g (32*e) a base s₀ s ∧
    Subsets n (context n) (layout n e).size m g (32*e) a base t₀ t
  refine (RelCT.loop I ?_ 31).mono ?_ (fun _ _ h => h)
  · intro remaining s t tr ur sf tf ⟨a,eq,ha,hi,S,T⟩ E F
    subst remaining
    obtain ⟨Trace,Agree⟩ := publicSubsetStep_relCT h base a ha hi _ _ _ _ _ _ ⟨S.ctx.scr,T.ctx.scr,S.count,T.count⟩ E F
    obtain ⟨S',Zs⟩ := wp_result (VG.Proof.Mont.X86.Comb.subsetStep_ok (table_layout h) S ha hi) E
    obtain ⟨T',Zt⟩ := wp_result (VG.Proof.Mont.X86.Comb.subsetStep_ok (table_layout h) T ha hi) F
    refine ⟨Trace,?_,fun _ => Agree,?_⟩
    · change VG.X86.eval .ne sf=VG.X86.eval .ne tf
      simp only [VG.X86.eval,Zs,Zt]
    · intro hc
      have next : a+1<32 := by
        by_contra hn
        have eq : a+1=32 := by omega
        change VG.X86.eval .ne sf=some true at hc
        simp only [VG.X86.eval,Zs,eq,decide_true,Option.map_some,Bool.not_true] at hc
        cases hc
      exact ⟨32-(a+1),by omega,a+1,rfl,by omega,next,S',T'⟩
  · intro s t ⟨S,T⟩
    exact ⟨1,rfl,by decide,by decide,S,T⟩

structure PublicSubsetsInput (n e m g : Nat) (base : Addr) (s : State) : Prop where
  ctx : Context n m base (layout n e).size s
  table : TableAt n (context n) m g (32*e) base (knownSubset 1) s.mem

theorem publicSubsets_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g : Nat) :
    RelCT isa (fun s t => PublicSubsetsInput n e m g base s ∧ PublicSubsetsInput n e m g base t)
      (VG.Impl.Mont.X86.Comb.buildSubsets n (context n))
      (VG.X86.Taint.Agree columnIndex) := by
  unfold VG.Impl.Mont.X86.Comb.buildSubsets
  let R := fun (s t : State) => ∃ s₀ t₀,
    Subsets n (context n) (layout n e).size m g (32*e) 1 base s₀ s ∧
    Subsets n (context n) (layout n e).size m g (32*e) 1 base t₀ t
  refine RelCT.seq (R := R) ?_ ?_
  · intro s t tr ur sf tf ⟨S,T⟩ Es Et
    have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.ctx.scr.edi_toNat.trans T.ctx.scr.edi_toNat.symm)
    have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
    have CT : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
        (.block [.mov .esi (VG.Impl.Mont.X86.Comb.imm 1)])
        (VG.X86.Taint.Agree (workspaceTaint false)) := checkedProgramChange (hint := .block []) rfl rfl
    exact ⟨(CT _ _ _ _ _ _ A Es Et).1,s,t,
      wp_result (VG.Proof.Mont.X86.Comb.buildSubsets_initial S.ctx S.table) Es,
      wp_result (VG.Proof.Mont.X86.Comb.buildSubsets_initial T.ctx T.table) Et⟩
  · intro s t tr ur sf tf ⟨s₀,t₀,S,T⟩ Es Et
    exact publicSubsetLoop_relCT h base m g s₀ t₀ _ _ _ _ _ _ ⟨S,T⟩ Es Et

end VG.Proof.Dsa.X86.Comb
