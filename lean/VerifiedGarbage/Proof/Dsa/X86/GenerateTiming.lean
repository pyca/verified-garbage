module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.CallMinusTiming
import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
import VerifiedGarbage.Proof.Dsa.X86.CallReduceTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Domain checking and derivation use fixed arithmetic schedules -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem generateDomain_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) :
    RelCT isa (CallPair L) (Generate.domain L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega)
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega)
  exact RelCT.seq (callRange_relCT L L.pLen .p (.input .g) true P G (by omega) (by omega) L.aligned.1)
    (RelCT.seq (callMinusP_relCT L t P (by decide) (by change 14944 + L.pLen ≤ 15712; omega))
    (RelCT.seq (callReduce_relCT L (.local t) (.imm (BitVec.ofNat 32 L.pLen)) L.pLen u (.inl ⟨_, rfl⟩)
      (fun s _ => LenOperand.imm _ _ _ s _) Q T (by omega) (by decide)
      (by change 14816 + L.qLen ≤ 15712; omega))
    (RelCT.seq (callZero_relCT L L.qLen (.local u) false U (by omega) (by omega) L.aligned.2)
      (RelCT.block_nil (fun _ _ h => h)))))

theorem generateSubgroup_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) :
    RelCT isa (CallPair L) (Generate.subgroup L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have bound : t + L.pLen ≤ usedBytes := by change 14944 + L.pLen ≤ 15712; omega
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.input .q) t P G Q (by decide) bound)
    (callOne_relCT L L.pLen (.local t) T (by omega) (by omega) L.aligned.1)

theorem generateParameters_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) :
    RelCT isa (CallPair L) (Generate.parameters L.pLen L.qLen) (CallPair L) :=
  RelCT.seq (generateDomain_relCT L P Q G) (generateSubgroup_relCT L P Q G)

theorem deriveCompute_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (X : CallOperand L (.input .nonce) L.qLen) :
    RelCT isa (CallPair L) (Generate.deriveCompute L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have bound : t2 + L.pLen ≤ usedBytes := by change 15328 + L.pLen ≤ 15712; omega
  have Y := CallOperand.localBuffer L t2 L.pLen (by decide) bound
  exact RelCT.seq (generateParameters_relCT L P Q G)
    (RelCT.seq (callRange_relCT L L.qLen .q (.input .nonce) false Q X (by omega) (by omega) L.aligned.2)
    (RelCT.seq (callPowerP_relCT L (.input .g) (.input .nonce) t2 P G X (by decide) bound)
    (RelCT.seq (callRange_relCT L L.pLen .p (.local t2) true P Y (by omega) (by omega) L.aligned.1)
      (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Dsa.X86
