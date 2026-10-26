module

public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Key copies reveal public addresses and component lengths only -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def keyCopyTaint : VG.X86.Taint.T :=
  { workspaceTaint false with regs := .ofList [.edi, .esi, .edx, .ecx] }

theorem keyCopyPart_relCT (input : Pointer) (len : Nat) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s input = pointerValue base t input ∧ s.gpr .edx = t.gpr .edx)
      (Generate.copyPart input len) (VG.X86.Taint.Agree keyCopyTaint) := by
  unfold Generate.copyPart
  refine RelCT.seq (R := VG.X86.Taint.Agree keyCopyTaint) ?_ ?_
  · apply RelCT.block_append
    refine RelCT.seq (R := VG.X86.Taint.Agree { keyCopyTaint with regs := .ofList [.edi, .esi, .edx] }) ?_ ?_
    · intro s t tr ur sf tf ⟨S, T, P, D⟩ E F
      have Trace := (pointer_relCT input base size hz _ _ _ _ _ _ ⟨S, T, P⟩ E F).1
      obtain ⟨PS, KS, _⟩ := wp_result (pointer_ok S hz input) E
      obtain ⟨PT, KT, _⟩ := wp_result (pointer_ok T hz input) F
      refine ⟨Trace, ?_⟩
      apply agree_regs (rs := [.edi, .esi, .edx])
      intro reg member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · rw [KS.1 _ (by decide), KT.1 _ (by decide)]
        exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
      · exact PS.trans (P.trans PT.symm)
      · rw [KS.1 _ (by decide), KT.1 _ (by decide)]; exact D
    · exact erased_relCT _ (.block [.mov .ecx (.imm 0)]) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
  · exact checkedProgramChange (τ' := { keyCopyTaint with flags := true })
      (hint := .loop keyCopyTaint (.block [])) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.Dsa.X86
