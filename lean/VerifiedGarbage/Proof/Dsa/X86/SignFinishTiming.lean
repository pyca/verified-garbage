module
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Weierstrass.PointContract

import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.CallProductTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreProductTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.CallReduceTiming
import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant-time signing arithmetic with reduced addition operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def SumReady (L : CallLayout) (s : State) : Prop :=
  operandValue s L.base (.local z) L.qLen < L.q ∧ operandValue s L.base (.local u) L.qLen < L.q

theorem signSumInputs_ok (L : CallLayout)
    (X : CallOperand L (.input .x) L.qLen) (D : CallOperand L (.input .digest) L.digestPrefix)
    (hd : L.digestPrefix < 2 ^ 32) (s0 : State) (R : CallReady L s0) :
    WP isa (.seq (Core.product L.qLen (.input .x) (.local r) u)
      (Core.reduce L.qLen Core.digestPrefix (.input .digest) z)) s0 (SumReady L) := by
  have W := L.lengths
  have N : (L.qLen + 7) / 8 ≤ 48 := by omega
  have qp : 0 < L.q := by have := R.moduli.qLarge; omega
  refine WP.seq (WP.mono (stageProduct_ok R.moduli (R.operand X (by omega) N)
    (R.moduli.scalarReady (by decide) N) (by decide) (R.moduli.scalarFit (by decide))) fun s1 ⟨M1, F1⟩ => ?_)
  have R1 := R.keep (F1.toStageFrame.execution (.inl ⟨by decide, R.moduli.scalarFit (by decide)⟩))
  have U1 := F1.scalar_value R.moduli (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) R.moduli.valueBounds.2)
  refine WP.mono (stageReduce_ok R1.prefixOperand M1 (R1.stream D (fun _ h => by cases h) N) (R1.stack D (fun _ h => by cases h)) hd (by decide) (M1.scalarFit (by decide))) fun s2 ⟨_, F2⟩ => ?_
  constructor
  · rw [F2.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M1.valueBounds.2)]
    exact Nat.mod_lt _ qp
  · rw [F2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide), U1]
    exact Nat.mod_lt _ qp

theorem signSum_relCT (L : CallLayout) (Q : CallOperand L (.input .q) L.qLen) :
    RelCT isa (fun s t => CallPair L s t ∧ SumReady L s ∧ SumReady L t)
      (Core.sum L.qLen (.local z) (.local u) v) (CallPair L) := by
  have W := L.lengths
  have Z := CallOperand.localBuffer L z L.qLen (by decide) (by change 14880 + L.qLen ≤ 15712; omega)
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega)
  have CT := coreSum_relCT L.base L.size L.qLen v (.local z) (.local u) L.saved (by omega) (by omega) L.aligned.2
  intro s t tr ur sf tf ⟨H, S, T⟩ E F
  have A : ArithmeticAgree L.base L.size L.qLen L.qLen .q (.local z) (.local u) s t :=
    ⟨H.1.arithmeticQ Z U, H.2.arithmeticQ Z U, H.pointer Q, H.pointer Z, H.pointer U⟩
  have frame (s : State) (R : CallReady L s) (B : SumReady L s) :
      WP isa (Core.sum L.qLen (.local z) (.local u) v) s (CallReady L) := by
    exact WP.mono (stageSum_ok R.moduli (R.operand Z (by omega) (by omega))
      (R.operand U (by omega) (by omega)) B.1 B.2 (by decide) (R.moduli.scalarFit (by decide)))
      fun _ H => R.keep (H.2.toStageFrame.execution (.inl ⟨by decide, R.moduli.scalarFit (by decide)⟩))
  exact ⟨(CT _ _ _ _ _ _ A E F).1, wp_result (frame s H.1 S) E, wp_result (frame t H.2 T) F⟩

theorem callSignFinish_relCT (L : CallLayout)
    (Q : CallOperand L (.input .q) L.qLen) (X : CallOperand L (.input .x) L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.signFinish L.qLen) (CallPair L) := by
  have W := L.lengths
  have R := CallOperand.localBuffer L r L.qLen (by decide) (by change 14720 + L.qLen ≤ 15712; omega)
  have I := CallOperand.localBuffer L inverse L.qLen (by decide) (by change 14784 + L.qLen ≤ 15712; omega)
  have V := CallOperand.localBuffer L v L.qLen (by decide) (by change 14848 + L.qLen ≤ 15712; omega)
  unfold Core.signFinish Core.sequence
  dsimp only [List.foldr]
  apply RelCT.assoc
  refine RelCT.seq ((RelCT.seq
    (callProductQ_relCT L (.input .x) (.local r) u Q X R (by decide) (by change 14816 + L.qLen ≤ 15712; omega))
    (callReduce_relCT (hl := fun _ h => by cases h) L (.input .digest) Core.digestPrefix L.digestPrefix z (.inr ⟨_, rfl⟩)
      (fun _ R => R.prefixOperand) Q D hd (by decide) (by change 14880 + L.qLen ≤ 15712; omega))).wp
    (fun s t H => ⟨signSumInputs_ok L X D hd s H.1, signSumInputs_ok L X D hd t H.2⟩)) ?_
  exact RelCT.seq (signSum_relCT L Q)
    (RelCT.seq (callProductQ_relCT L (.local inverse) (.local v) VG.Impl.Dsa.Layout.s Q I V
      (by decide) (by change 14752 + L.qLen ≤ 15712; omega)) (RelCT.block_nil (fun _ _ h => h)))

end VG.Proof.Dsa.X86
