module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Dsa.X86.Comb.ParametersTiming
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! The comb checker branches on public shape and public parameter values. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem checkingSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p,L.pLen)∈L.inputs) (Q : (.input .q,L.qLen)∈L.inputs)
    (G : (.input .g,L.pLen)∈L.inputs)
    (stable : ∀ input∈L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix=min digestLen (Spec.Dsa.bitLength L.q/8))
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t ∧
      operandValue s L.base (.input .g) L.pLen=operandValue t L.base (.input .g) L.pLen)
      (checkSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let R := fun s t => VG.X86.Taint.Agree (workspaceTaint false) s t ∧
    (shapeValid L.p L.q → PublicGenerator L s t)
  change RelCT isa _ (.seq (Shape.check L.pLen L.qLen) (.ite .e _ _)) _
  refine RelCT.seq (M := isa) (R := fun s t => R s t ∧ s.zf=some (!decide (shapeValid L.p L.q)) ∧
      t.zf=some (!decide (shapeValid L.p L.q))) ?_
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  · intro s t tr ur sf tf ⟨S,T,Eq⟩ E F
    have CT := shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ ⟨S,T⟩ E F
    obtain ⟨Zs,Ms,Ks,Fs⟩ := wp_result (shapeCall_ok S P Q stable hd) E
    obtain ⟨Zt,Mt,Kt,Ft⟩ := wp_result (shapeCall_ok T P Q stable hd) F
    have bound : 8248≤L.size := by have := L.extent; change 15712≤L.size at this; omega
    have Es := (S.buffers _ G).value_keep_shape Fs Ks (by decide)
      (by change ShapePointer (.input .g); decide) bound
    have Et := (T.buffers _ G).value_keep_shape Ft Kt (by decide)
      (by change ShapePointer (.input .g); decide) bound
    exact ⟨CT.1,⟨CT.2.1.1,fun h => ⟨⟨(Ms h).ready,(Mt h).ready⟩,Es.trans (Eq.trans Et.symm)⟩⟩,Zs,Zt⟩
  · by_cases valid : shapeValid L.p L.q
    · simp only [valid,decide_true,Bool.not_true,Bool.false_eq_true,ite_false]
      exact (RelCT.seq (parameters_relCT L (.inl ⟨_,P,Nat.le_refl _⟩)
        (.inl ⟨_,Q,Nat.le_refl _⟩) G fits)
        (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))).mono
        (fun _ _ H => H.2 valid) (fun _ _ h => h)
    · simp only [valid,decide_false,Bool.not_false,ite_true]
      exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

end VG.Proof.Dsa.X86.Comb
