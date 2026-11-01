module
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming

import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.CallMinusTiming
import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
import VerifiedGarbage.Proof.Dsa.X86.CallReduceTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Constant-time domain and key validation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallOperand.localBuffer (L : CallLayout) (offset len : Nat)
    (lo : r ≤ offset) (hi : offset + len ≤ usedBytes) : CallOperand L (.local offset) len :=
  .inr ⟨offset, rfl, lo, hi⟩

theorem callDomain_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Validate.domain L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega)
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega)
  have A := L.aligned
  exact RelCT.seq (RelCT.seq
    (callRange_relCT L L.pLen .p (.input .g) true P G (by omega) (by omega) A.1)
    (callRange_relCT L L.pLen .p (.input .y) true P Y (by omega) (by omega) A.1))
    (RelCT.seq (callMinusP_relCT L t P (by decide) (by change 14944 + L.pLen ≤ 15712; omega))
    (RelCT.seq (callReduce_relCT (hl := fun _ _ => by have := L.lengths; omega) L (.local t) (.imm (BitVec.ofNat 32 L.pLen)) L.pLen u (.inl ⟨_, rfl⟩)
      (fun s _ => LenOperand.imm _ _ _ s _) Q T (by omega) (by decide)
      (by change 14816 + L.qLen ≤ 15712; omega))
    (RelCT.seq (callZero_relCT L L.qLen (.local u) false U (by omega) (by omega) A.2)
    (RelCT.seq (callMinusQ_relCT L qMinusTwo Q (by decide)
      (by change 14912 + L.qLen ≤ 15712; omega)) (RelCT.block_nil (fun _ _ h => h))))))

theorem callSubgroup_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Validate.subgroup L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have bound : t + L.pLen ≤ usedBytes := by change 14944 + L.pLen ≤ 15712; omega
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  have A := L.aligned
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.input .q) t P G Q (by decide) bound)
    (RelCT.seq (callOne_relCT L L.pLen (.local t) T (by omega) (by omega) A.1)
    (RelCT.seq (callPowerP_relCT L (.input .y) (.input .q) t P Y Q (by decide) bound)
    (RelCT.seq (callOne_relCT L L.pLen (.local t) T (by omega) (by omega) A.1)
      (RelCT.block_nil (fun _ _ h => h)))))

theorem callPublicKey_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Validate.publicKey L.pLen L.qLen) (CallPair L) :=
  RelCT.seq (callDomain_relCT L P Q G Y) (callSubgroup_relCT L P Q G Y)

theorem callPrivateKey_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (X : CallOperand L (.input .x) L.qLen) (K : CallOperand L (.input .nonce) L.qLen) :
    RelCT isa (CallPair L) (Validate.privateKey L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have bound : t + L.pLen ≤ usedBytes := by change 14944 + L.pLen ≤ 15712; omega
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  have A := L.aligned
  exact RelCT.seq (RelCT.seq
    (callRange_relCT L L.qLen .q (.input .x) false Q X (by omega) (by omega) A.2)
    (callRange_relCT L L.qLen .q (.input .nonce) false Q K (by omega) (by omega) A.2))
    (RelCT.seq (callPowerP_relCT L (.input .g) (.input .x) t P G X (by decide) bound)
    (RelCT.seq (callEqual_relCT L L.pLen (.local t) (.input .y) T Y (by omega) (by omega) A.1)
      (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Dsa.X86
