module

public import VerifiedGarbage.Proof.Dsa.X86.KeyOutputReady
public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core

import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveCompute
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.Comb.StageTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.ValidateRange
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
/-! Private comb computation followed by the shared output copies. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DeriveComputeTiming.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def DomainReady (L : CallLayout) (s : State) : Prop :=
  let g := operandValue s L.base (.input .g) L.pLen
  (1<g ∧ g<L.p) ∧ (L.p-1)%L.q=0 ∧ g^L.q%L.p=1

theorem deriveBody_relCT (L : CallLayout) (out : BitVec 32)
    (P : (.input .p,L.pLen)∈L.inputs) (Q : (.input .q,L.qLen)∈L.inputs)
    (G : (.input .g,L.pLen)∈L.inputs) (X : (.input .nonce,L.qLen)∈L.inputs)
    (Params : (.input .p,2*L.pLen+L.qLen)∈L.inputs)
    (ho : out.toNat+(3*L.pLen+2*L.qLen)≤2^32)
    (A : Region.Disjoint ⟨L.base,L.size⟩ ⟨out.setWidth 64,3*L.pLen+2*L.qLen⟩)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t ∧
      ContextReady L s ∧ ContextReady L t ∧ DomainReady L s ∧ DomainReady L t)
      (.seq (deriveCompute L.pLen L.qLen) (Generate.writeKey L.pLen L.qLen))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have W := L.lengths
  refine RelCT.seq (R := fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t) ?_ ?_
  · intro s t tr ur sf tf ⟨Pair,S,T,Cs,Ct,Ds,Dt⟩ E F
    have H := deriveCompute_relCT L (.inl ⟨_,P,Nat.le_refl _⟩) (.inl ⟨_,Q,Nat.le_refl _⟩)
      G X fits _ _ _ _ _ _ ⟨Pair,Cs,Ct⟩ E F
    have Es := (wp_result (deriveCompute_ok Pair.1.moduli (Pair.1.buffers _ G)
      (Pair.1.buffers _ X) rfl rfl Ds fits Cs) E).2.2.2
    have Et := (wp_result (deriveCompute_ok Pair.2.moduli (Pair.2.buffers _ G)
      (Pair.2.buffers _ X) rfl rfl Dt fits Ct) F).2.2.2
    exact ⟨H.1,H.2,S.keep Es,T.keep Et⟩
  · apply (writeKey_relCT L.base L.size L.pLen L.qLen out L.saved ho (by omega) A).mono ?_ (fun _ _ h => h)
    intro s t ⟨Pair,S,T⟩
    exact ⟨S.writeReady Pair.1 Params X A,T.writeReady Pair.2 Params X A,
      Pair.pointer (.inl ⟨_,P,Nat.le_refl _⟩),Pair.pointer (.inl ⟨_,X,Nat.le_refl _⟩)⟩

end VG.Proof.Dsa.X86.Comb
