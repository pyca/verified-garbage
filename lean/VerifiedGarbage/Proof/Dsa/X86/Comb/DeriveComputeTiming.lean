module

public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
public import VerifiedGarbage.Proof.Dsa.X86.Comb.StageTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.ValidateRange
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! The private schedule uses the retained context and never branches on x. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

def ContextReady (L : CallLayout) (s : State) : Prop :=
  canonical ((L.pLen+7)/8) ((L.qLen+3)/4) L.p (operandValue s L.base (.input .g) L.pLen) L.base s.mem

theorem deriveCompute_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : (.input .g,L.pLen)∈L.inputs) (X : (.input .nonce,L.qLen)∈L.inputs)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => CallPair L s t ∧ ContextReady L s ∧ ContextReady L t)
      (deriveCompute L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have nq : (L.qLen+7)/8≤48 := by omega
  have Xop : CallOperand L (.input .nonce) L.qLen := .inl ⟨_,X,Nat.le_refl _⟩
  have Gop : CallOperand L (.input .g) L.pLen := .inl ⟨_,G,Nat.le_refl _⟩
  have bound : t2+L.pLen≤usedBytes := by change 15328+L.pLen≤15712; omega
  have Y := CallOperand.localBuffer L t2 L.pLen (by decide) bound
  unfold deriveCompute Core.sequence
  dsimp only [List.foldr]
  refine RelCT.seq (R := fun s t => CallPair L s t ∧ ContextReady L s ∧ ContextReady L t) ?_
    (RelCT.seq ?_ (RelCT.seq
      (callRange_relCT L L.pLen .p (.local t2) true P Y (by omega) (by omega) L.aligned.1)
      (RelCT.block_nil (fun _ _ h => h))))
  · intro s t tr ur sf tf ⟨Pair,Cs,Ct⟩ E F
    have H := callRange_relCT L L.qLen .q (.input .nonce) false Q Xop
      (by omega) (by omega) L.aligned.2 _ _ _ _ _ _ Pair E F
    have keep {u v : State} (R : CallReady L u) (C : ContextReady L u)
        {trace : List Leak} (Ev : Exec isa (Validate.range L.qLen .q (.input .nonce) false) u trace v) :
        ContextReady L v := by
      obtain ⟨_,K,O⟩ := wp_result (validateRange_ok R.moduli.scr L.saved rfl
        (by omega) (by omega) L.aligned.2 R.moduli.qReady
        ((R.buffers _ X).ready (R.moduli.context nq)) false) Ev
      have Ex := (StageFrame.of_frame K (by decide) O nq).execution (.inr ⟨rfl,rfl⟩)
      unfold ContextReady
      rw [Ex.value (R.buffers _ G) (by change StablePointer (.input .g); decide) L.extent]
      exact canonical_check (supported_widths L.widths) nq C O
    exact ⟨H.1,H.2,keep Pair.1 Cs E,keep Pair.2 Ct F⟩
  · apply (stagePower_relCT false L (.input .g) (.input .nonce) t2 P Gop Xop (by decide) fits).mono
      ?_ (fun _ _ H => H)
    intro s t ⟨Pair,Cs,Ct⟩
    exact ⟨Pair,fun h => Bool.noConfusion h,fun _ => ⟨Cs,Ct⟩⟩

end VG.Proof.Dsa.X86.Comb
