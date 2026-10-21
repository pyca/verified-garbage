module

public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
import VerifiedGarbage.Proof.Dsa.X86.Comb.StageTiming
import VerifiedGarbage.Proof.Dsa.X86.GenerateTiming
import VerifiedGarbage.Proof.Dsa.X86.GenerateDomain
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Dsa.X86.Comb
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming

/-! Public parameter preparation may branch only on the public domain values. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def PublicGenerator (L : CallLayout) (s t : State) : Prop :=
  CallPair L s t ∧ operandValue s L.base (.input .g) L.pLen=operandValue t L.base (.input .g) L.pLen

theorem parameters_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : (.input .g,L.pLen)∈L.inputs)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (PublicGenerator L) (parameters L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have Gop : CallOperand L (.input .g) L.pLen := .inl ⟨_,G,Nat.le_refl _⟩
  have bound : t+L.pLen≤usedBytes := by change 14944+L.pLen≤15712; omega
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  change RelCT isa (PublicGenerator L) (.seq (Generate.domain L.pLen L.qLen)
    (.seq (power true L.pLen L.qLen .p (.input .g) (.input .q) t)
      (Validate.isOne L.pLen (.local t)))) (CallPair L)
  refine RelCT.seq (R := PublicGenerator L) ?_ (RelCT.seq ?_
    (callOne_relCT L L.pLen (.local t) T (by omega) (by omega) L.aligned.1))
  · intro s t tr ur sf tf ⟨Pair,Eq⟩ E F
    have H := generateDomain_relCT L P Q Gop _ _ _ _ _ _ Pair E F
    have Es := (wp_result (generateDomain_ok Pair.1.moduli (Pair.1.buffers _ G) rfl) E).2.2
    have Et := (wp_result (generateDomain_ok Pair.2.moduli (Pair.2.buffers _ G) rfl) F).2.2
    exact ⟨H.1,H.2,(Es.value (Pair.1.buffers _ G) (by change StablePointer (.input .g); decide) L.extent).trans
      (Eq.trans (Et.value (Pair.2.buffers _ G) (by change StablePointer (.input .g); decide) L.extent).symm)⟩
  · apply (stagePower_relCT true L (.input .g) (.input .q) _ P Gop Q (by decide) fits).mono
      ?_ (fun _ _ H => H)
    intro s t ⟨Pair,Eq⟩
    exact ⟨Pair,fun _ => ⟨Eq,Pair.1.moduli.qValue.trans Pair.2.moduli.qValue.symm⟩,
      fun h => Bool.noConfusion h⟩

end VG.Proof.Dsa.X86.Comb
