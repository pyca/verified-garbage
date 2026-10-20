module

import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
public import VerifiedGarbage.Proof.Dsa.X86.OutputCall
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Public shape rejection for signing -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingShape_relCT (L : CallLayout) (digestLen : Nat) (out : BitVec 32)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => (ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t) ∧
      OutputCallReady L out s ∧ OutputCallReady L out t)
      (Shape.check L.pLen L.qLen)
      (fun s t => ((VG.X86.Taint.Agree (workspaceTaint false) s t ∧
        (shapeValid L.p L.q → ShapedCall L digestLen s ∧ ShapedCall L digestLen t)) ∧
        OutputCallReady L out s ∧ OutputCallReady L out t) ∧
        s.zf = some (!decide (shapeValid L.p L.q)) ∧ t.zf = some (!decide (shapeValid L.p L.q))) := by
  intro s t tr ur sf tf ⟨H, S, T⟩ E F
  obtain ⟨trace, A, Z1, Z2⟩ := shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ H E F
  obtain ⟨_, _, K1, O1⟩ := wp_result (shapeCall_ok H.1 P Q stable hd) E
  obtain ⟨_, _, K2, O2⟩ := wp_result (shapeCall_ok H.2 P Q stable hd) F
  exact ⟨trace, ⟨A, S.keepShape K1 (by decide) (by decide) O1,
    T.keepShape K2 (by decide) (by decide) O2⟩, Z1, Z2⟩

theorem signSized_relCT (L : CallLayout) (digestLen : Nat) (out : BitVec 32)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (D : (.input .digest, digestLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => (ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t) ∧
      OutputCallReady L out s ∧ OutputCallReady L out t)
      (Entry.sized true L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Entry.sized
  refine RelCT.seq (signingShape_relCT L digestLen out P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have B := shape_digest_width valid
    have CT := callSignBody_relCT L out (.inl ⟨_, P, Nat.le_refl _⟩) (.inl ⟨_, Q, Nat.le_refl _⟩)
      G Y X K ⟨_, D, by rw [hd]; exact Nat.min_le_left _ _⟩ (by rw [hd]; omega)
    exact CT.mono (fun _ _ H => ⟨⟨(H.1.2 True.intro).1.ready, (H.1.2 True.intro).2.ready⟩,
      H.2.1.signature (H.1.2 True.intro).1, H.2.2.signature (H.1.2 True.intro).2⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact (signFailure_relCT L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.2.1.scr, H.2.2.scr, H.2.1.pointer.trans H.2.2.pointer.symm,
        H.2.1.qLength.trans H.2.2.qLength.symm⟩) (fun _ _ h => h)

end VG.Proof.Dsa.X86
