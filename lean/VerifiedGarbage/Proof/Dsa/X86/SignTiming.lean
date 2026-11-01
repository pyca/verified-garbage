module
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Weierstrass.PointContract

import VerifiedGarbage.Proof.Dsa.X86.SignFinishTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.CallReduceTiming
import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant-time signing computation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callSignStart_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (K : CallOperand L (.input .nonce) L.qLen) :
    RelCT isa (CallPair L) (Core.signStart L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega)
  have E := CallOperand.localBuffer L qMinusTwo L.qLen (by decide) (by change 14912 + L.qLen ≤ 15712; omega)
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.input .nonce) t P G K (by decide)
    (by change 14944 + L.pLen ≤ 15712; omega))
    (RelCT.seq (callReduce_relCT (hl := fun _ _ => by have := L.lengths; omega) L (.local t) (.imm (BitVec.ofNat 32 L.pLen)) L.pLen r (.inl ⟨_, rfl⟩)
      (fun s _ => LenOperand.imm _ _ _ s _) Q T (by omega) (by decide)
      (by change 14720 + L.qLen ≤ 15712; omega))
    (RelCT.seq (callPowerQ_relCT L (.input .nonce) (.local qMinusTwo) inverse Q K E (by decide)
      (by change 14784 + L.qLen ≤ 15712; omega)) (RelCT.block_nil (fun _ _ h => h))))

theorem callSign_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (K : CallOperand L (.input .nonce) L.qLen)
    (X : CallOperand L (.input .x) L.qLen) (D : CallOperand L (.input .digest) L.digestPrefix)
    (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.sign L.pLen L.qLen) (CallPair L) :=
  RelCT.seq (callSignStart_relCT L P Q G K) (callSignFinish_relCT L Q X D hd)

theorem callSignCompute_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (K : CallOperand L (.input .nonce) L.qLen) (X : CallOperand L (.input .x) L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (SignVerify.signCompute L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have R := CallOperand.localBuffer L r L.qLen (by decide) (by change 14720 + L.qLen ≤ 15712; omega)
  have S := CallOperand.localBuffer L s L.qLen (by decide) (by change 14752 + L.qLen ≤ 15712; omega)
  exact RelCT.seq (callPublicKey_relCT L P Q G Y)
    (RelCT.seq (callPrivateKey_relCT L P Q G Y X K)
    (RelCT.seq (callSign_relCT L P Q G K X D hd)
    (RelCT.seq (RelCT.seq
      (callZero_relCT L L.qLen (.local r) true R (by omega) (by omega) L.aligned.2)
      (callZero_relCT L L.qLen (.local s) true S (by omega) (by omega) L.aligned.2))
      (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Dsa.X86
