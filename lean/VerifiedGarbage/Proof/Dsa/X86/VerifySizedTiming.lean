module

import VerifiedGarbage.Proof.Dsa.OutputBytes
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.ShapeTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Complete public shape rejection and verification -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem shapeCall_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Shape.check L.pLen L.qLen)
      (fun s t => (VG.X86.Taint.Agree (workspaceTaint false) s t ∧
        (shapeValid L.p L.q → ShapedCall L digestLen s ∧ ShapedCall L digestLen t)) ∧
        s.zf = some (!decide (shapeValid L.p L.q)) ∧ t.zf = some (!decide (shapeValid L.p L.q))) := by
  have W := L.lengths
  intro s t tr ur sf tf ⟨S, T⟩ E F
  have ctx : VG.Impl.Mont.X86.Dynamic.contextBytes 48 ≤ L.size := by
    have H : 15712 ≤ L.size := L.extent
    change 7048 ≤ L.size; omega
  obtain ⟨trace, A⟩ := shape_relCT L.pLen L.qLen L.base L.size L.saved (by omega) (by omega) L.aligned.1
    _ _ _ _ _ _ ⟨S.scr, T.scr, (S.buffers _ P).ready ctx, (T.buffers _ P).ready ctx,
      (S.pointers _ P).trans (T.pointers _ P).symm, (S.pointers _ Q).trans (T.pointers _ Q).symm⟩ E F
  obtain ⟨Z1, M1, _, _⟩ := wp_result (shapeCall_ok S P Q stable hd) E
  obtain ⟨Z2, M2, _, _⟩ := wp_result (shapeCall_ok T P Q stable hd) F
  exact ⟨trace, ⟨A, fun h => ⟨M1 h, M2 h⟩⟩, Z1, Z2⟩

theorem verifySized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (R : (.input .signature, L.qLen) ∈ L.inputs) (S : (.signatureS, L.qLen) ∈ L.inputs)
    (D : (.input .digest, digestLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Entry.sized false L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Entry.sized
  refine RelCT.seq (shapeCall_relCT L digestLen P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have B := shape_digest_width valid
    have CT := callVerifyBody_relCT L (.inl ⟨_, P, Nat.le_refl _⟩) (.inl ⟨_, Q, Nat.le_refl _⟩)
      (.inl ⟨_, G, Nat.le_refl _⟩) (.inl ⟨_, Y, Nat.le_refl _⟩)
      (.inl ⟨_, R, Nat.le_refl _⟩) (.inl ⟨_, S, Nat.le_refl _⟩)
      (.inl ⟨_, D, by rw [hd]; exact Nat.min_le_left _ _⟩) (by rw [hd]; omega)
    exact CT.mono (fun _ _ H => ⟨(H.2 True.intro).1.ready, (H.2 True.intro).2.ready⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

end VG.Proof.Dsa.X86
