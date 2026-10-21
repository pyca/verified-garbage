module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Dsa.X86.GenerateTiming

/-! # Domain checking branches only on the public shape -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Generate.checkSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Generate.checkSized
  refine RelCT.seq (shapeCall_relCT L digestLen P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have CT := RelCT.seq (generateParameters_relCT L (.inl ⟨_, P, Nat.le_refl _⟩)
      (.inl ⟨_, Q, Nat.le_refl _⟩) (.inl ⟨_, G, Nat.le_refl _⟩))
      (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))
    exact CT.mono (fun _ _ H => ⟨(H.2 True.intro).1.ready, (H.2 True.intro).2.ready⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

end VG.Proof.Dsa.X86
