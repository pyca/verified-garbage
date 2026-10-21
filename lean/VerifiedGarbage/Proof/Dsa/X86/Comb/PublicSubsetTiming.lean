module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSubsetAccessTiming
public import VerifiedGarbage.Proof.Mont.X86.CombSubsets
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Subset completion uses a public counter for both direct table accesses. -/

@[expose] public section
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
