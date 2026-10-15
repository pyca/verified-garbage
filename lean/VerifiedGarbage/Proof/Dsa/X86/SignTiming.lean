module

public import VerifiedGarbage.Proof.Dsa.X86.SignFinishTiming

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
    (RelCT.seq (callReduce_relCT L (.local t) L.pLen r Q T (by omega) (by decide)
      (by change 14720 + L.qLen ≤ 15712; omega))
    (RelCT.seq (callPowerQ_relCT L (.input .nonce) (.local qMinusTwo) inverse Q K E (by decide)
      (by change 14784 + L.qLen ≤ 15712; omega)) (RelCT.block_nil (fun _ _ h => h))))

theorem callSign_relCT (L : CallLayout) (digestLen : Nat)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (K : CallOperand L (.input .nonce) L.qLen)
    (X : CallOperand L (.input .x) L.qLen) (D : CallOperand L (.input .digest) digestLen)
    (hd : digestLen < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.sign L.pLen L.qLen digestLen) (CallPair L) :=
  RelCT.seq (callSignStart_relCT L P Q G K) (callSignFinish_relCT L digestLen Q X D hd)

theorem callSignCompute_relCT (L : CallLayout) (digestLen : Nat)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (K : CallOperand L (.input .nonce) L.qLen) (X : CallOperand L (.input .x) L.qLen)
    (D : CallOperand L (.input .digest) digestLen) (hd : digestLen < 2 ^ 32) :
    RelCT isa (CallPair L) (SignVerify.signCompute L.pLen L.qLen digestLen) (CallPair L) := by
  have W := L.lengths
  have R := CallOperand.localBuffer L r L.qLen (by decide) (by change 14720 + L.qLen ≤ 15712; omega)
  have S := CallOperand.localBuffer L s L.qLen (by decide) (by change 14752 + L.qLen ≤ 15712; omega)
  exact RelCT.seq (callPublicKey_relCT L P Q G Y)
    (RelCT.seq (callPrivateKey_relCT L P Q G Y X K)
    (RelCT.seq (callSign_relCT L digestLen P Q G K X D hd)
    (RelCT.seq (RelCT.block_append (RelCT.seq
      (callZero_relCT L L.qLen (.local r) true R (by omega) (by omega))
      (callZero_relCT L L.qLen (.local s) true S (by omega) (by omega))))
      (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Dsa.X86
