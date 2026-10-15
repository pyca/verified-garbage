module

public import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
public import VerifiedGarbage.Proof.Dsa.X86.CallProductTiming
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify

/-! # Constant-time verification arithmetic and validation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callVerifyScalars_relCT (L : CallLayout) (digestLen : Nat)
    (Q : CallOperand L (.input .q) L.qLen) (R : CallOperand L (.input .signature) L.qLen)
    (S : CallOperand L .signatureS L.qLen) (D : CallOperand L (.input .digest) digestLen)
    (hd : digestLen < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.verifyScalars L.qLen digestLen) (CallPair L) := by
  have W := L.lengths
  have E := CallOperand.localBuffer L qMinusTwo L.qLen (by decide) (by change 14912 + L.qLen ≤ 15712; omega)
  have I := CallOperand.localBuffer L inverse L.qLen (by decide) (by change 14784 + L.qLen ≤ 15712; omega)
  have Z := CallOperand.localBuffer L z L.qLen (by decide) (by change 14880 + L.qLen ≤ 15712; omega)
  exact RelCT.seq (callPowerQ_relCT L .signatureS (.local qMinusTwo) inverse Q S E (by decide) (by change 14784 + L.qLen ≤ 15712; omega))
    (RelCT.seq (callReduce_relCT L (.input .digest) digestLen z Q D hd (by decide) (by change 14880 + L.qLen ≤ 15712; omega))
    (RelCT.seq (callProductQ_relCT L (.local z) (.local inverse) u Q Z I (by decide) (by change 14816 + L.qLen ≤ 15712; omega))
    (RelCT.seq (callProductQ_relCT L (.input .signature) (.local inverse) v Q R I (by decide) (by change 14848 + L.qLen ≤ 15712; omega))
    (RelCT.block_nil (fun _ _ h => h)))))

theorem callVerifyPowers_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Core.verifyPowers L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega)
  have V := CallOperand.localBuffer L v L.qLen (by decide) (by change 14848 + L.qLen ≤ 15712; omega)
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega)
  have T2 := CallOperand.localBuffer L t2 L.pLen (by decide) (by change 15328 + L.pLen ≤ 15712; omega)
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.local u) t P G U (by decide) (by change 14944 + L.pLen ≤ 15712; omega))
    (RelCT.seq (callPowerP_relCT L (.input .y) (.local v) t2 P Y V (by decide) (by change 15328 + L.pLen ≤ 15712; omega))
    (RelCT.seq (callProductP_relCT L (.local t) (.local t2) t P T T2 (by decide) (by change 14944 + L.pLen ≤ 15712; omega))
    (RelCT.seq (callReduce_relCT L (.local t) L.pLen u Q T (by omega) (by decide) (by change 14816 + L.qLen ≤ 15712; omega))
    (RelCT.block_nil (fun _ _ h => h)))))

theorem callVerify_relCT (L : CallLayout) (digestLen : Nat)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (R : CallOperand L (.input .signature) L.qLen) (S : CallOperand L .signatureS L.qLen)
    (D : CallOperand L (.input .digest) digestLen) (hd : digestLen < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.verify L.pLen L.qLen digestLen) (CallPair L) :=
  RelCT.seq (callVerifyScalars_relCT L digestLen Q R S D hd) (callVerifyPowers_relCT L P Q G Y)

theorem callVerifyCompute_relCT (L : CallLayout) (digestLen : Nat)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (R : CallOperand L (.input .signature) L.qLen) (S : CallOperand L .signatureS L.qLen)
    (D : CallOperand L (.input .digest) digestLen) (hd : digestLen < 2 ^ 32) :
    RelCT isa (CallPair L) (SignVerify.verifyCompute L.pLen L.qLen digestLen) (CallPair L) := by
  have W := L.lengths
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega)
  exact RelCT.seq (callPublicKey_relCT L P Q G Y)
    (RelCT.seq (RelCT.block_append (RelCT.seq (callRange_relCT L L.qLen .q (.input .signature) false Q R (by omega) (by omega))
      (callRange_relCT L L.qLen .q .signatureS false Q S (by omega) (by omega))))
    (RelCT.seq (callVerify_relCT L digestLen P Q G Y R S D hd)
    (RelCT.seq (callEqual_relCT L L.qLen (.local u) (.input .signature) U R (by omega) (by omega))
    (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Dsa.X86
