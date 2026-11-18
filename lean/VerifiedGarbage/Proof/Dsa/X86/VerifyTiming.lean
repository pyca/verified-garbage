module

import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.CallProductTiming
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.PrivateKey
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! ### `Dsa.X86.SignTiming`, which the modules that import this one used -/

section

/-! ### `Dsa.X86.SignFinishTiming`, which only this module used -/

section

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
  have N : (L.qLen + 7) / 8 ≤ 48 := by omega_using [W]
  have qp : 0 < L.q := by have := R.moduli.qLarge; omega_using [this]
  refine WP.seq (WP.mono (stageProduct_ok R.moduli (R.operand X (by omega_using [W]) N)
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
  have Z := CallOperand.localBuffer L z L.qLen (by decide) (by change 14880 + L.qLen ≤ 15712; omega_using [W])
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W])
  have CT := coreSum_relCT L.base L.size L.qLen v (.local z) (.local u) L.saved (by omega_using [W]) (by omega_using [W]) L.aligned.2
  intro s t tr ur sf tf ⟨H, S, T⟩ E F
  have A : ArithmeticAgree L.base L.size L.qLen L.qLen .q (.local z) (.local u) s t :=
    ⟨H.1.arithmeticQ Z U, H.2.arithmeticQ Z U, H.pointer Q, H.pointer Z, H.pointer U⟩
  have frame (s : State) (R : CallReady L s) (B : SumReady L s) :
      WP isa (Core.sum L.qLen (.local z) (.local u) v) s (CallReady L) := by
    exact WP.mono (stageSum_ok R.moduli (R.operand Z (by omega_using [W]) (by omega_using [W]))
      (R.operand U (by omega_using [W]) (by omega_using [W])) B.1 B.2 (by decide) (R.moduli.scalarFit (by decide)))
      fun _ H => R.keep (H.2.toStageFrame.execution (.inl ⟨by decide, R.moduli.scalarFit (by decide)⟩))
  exact ⟨(CT _ _ _ _ _ _ A E F).1, wp_result (frame s H.1 S) E, wp_result (frame t H.2 T) F⟩

theorem callSignFinish_relCT (L : CallLayout)
    (Q : CallOperand L (.input .q) L.qLen) (X : CallOperand L (.input .x) L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.signFinish L.qLen) (CallPair L) := by
  have W := L.lengths
  have R := CallOperand.localBuffer L r L.qLen (by decide) (by change 14720 + L.qLen ≤ 15712; omega_using [W])
  have I := CallOperand.localBuffer L inverse L.qLen (by decide) (by change 14784 + L.qLen ≤ 15712; omega_using [W])
  have V := CallOperand.localBuffer L v L.qLen (by decide) (by change 14848 + L.qLen ≤ 15712; omega_using [W])
  unfold Core.signFinish Core.sequence
  dsimp only [List.foldr]
  apply RelCT.assoc
  refine RelCT.seq ((RelCT.seq
    (callProductQ_relCT L (.input .x) (.local r) u Q X R (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W]))
    (callReduce_relCT (hl := fun _ h => by cases h) L (.input .digest) Core.digestPrefix L.digestPrefix z (.inr ⟨_, rfl⟩)
      (fun _ R => R.prefixOperand) Q D hd (by decide) (by change 14880 + L.qLen ≤ 15712; omega_using [W]))).wp
    (fun s t H => ⟨signSumInputs_ok L X D hd s H.1, signSumInputs_ok L X D hd t H.2⟩)) ?_
  exact RelCT.seq (signSum_relCT L Q)
    (RelCT.seq (callProductQ_relCT L (.local inverse) (.local v) VG.Impl.Dsa.Layout.s Q I V
      (by decide) (by change 14752 + L.qLen ≤ 15712; omega_using [W])) (RelCT.block_nil (fun _ _ h => h)))

end VG.Proof.Dsa.X86

end

end


/-! # Constant-time signing computation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callSignStart_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (K : CallOperand L (.input .nonce) L.qLen) :
    RelCT isa (CallPair L) (Core.signStart L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W])
  have E := CallOperand.localBuffer L qMinusTwo L.qLen (by decide) (by change 14912 + L.qLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.input .nonce) t P G K (by decide)
    (by change 14944 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callReduce_relCT (hl := fun _ _ => by have := L.lengths; omega_using [W]) L (.local t) (.imm (BitVec.ofNat 32 L.pLen)) L.pLen r (.inl ⟨_, rfl⟩)
      (fun s _ => LenOperand.imm _ _ _ s _) Q T (by omega_using [W]) (by decide)
      (by change 14720 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callPowerQ_relCT L (.input .nonce) (.local qMinusTwo) inverse Q K E (by decide)
      (by change 14784 + L.qLen ≤ 15712; omega_using [W])) (RelCT.block_nil (fun _ _ h => h))))

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
  have R := CallOperand.localBuffer L r L.qLen (by decide) (by change 14720 + L.qLen ≤ 15712; omega_using [W])
  have S := CallOperand.localBuffer L s L.qLen (by decide) (by change 14752 + L.qLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPublicKey_relCT L P Q G Y)
    (RelCT.seq (callPrivateKey_relCT L P Q G Y X K)
    (RelCT.seq (callSign_relCT L P Q G K X D hd)
    (RelCT.seq (RelCT.seq
      (callZero_relCT L L.qLen (.local r) true R (by omega_using [W]) (by omega_using [W]) L.aligned.2)
      (callZero_relCT L L.qLen (.local s) true S (by omega_using [W]) (by omega_using [W]) L.aligned.2))
      (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.SignCompute`, which the modules that import this one used -/

section

/-! # Signing arithmetic and all post-shape acceptance conditions -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SignFinish.lean`, which only this module imported.
section

/-! # The remaining scalar arithmetic of a signing attempt -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signFinish_ok {base : Addr} {size pLen qLen p q digestLen x digest rv inv : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (X : CallerBuffer s0 base size (.input .x) qLen) (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hx : operandValue s0 base (.input .x) qLen = x) (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hr : operandValue s0 base (.local r) qLen = rv)
    (hi : operandValue s0 base (.local VG.Impl.Dsa.Layout.inverse) qLen = inv) :
    WP isa (Core.signFinish qLen) s0 fun s4 =>
      Moduli base size pLen qLen p q s4 ∧ operandValue s4 base (.local r) qLen = rv ∧
      operandValue s4 base (.local VG.Impl.Dsa.Layout.s) qLen = inv * ((digest % q + x * rv % q) % q) % q ∧
      Execution base s0 s4 ∧
      flagW base (Layout.field .mask) s4 = flagW base (Layout.field .mask) s0 := by
  have L := M.lengths
  obtain nq : (qLen + 7) / 8 ≤ 48 := by omega
  obtain qp : 0 < q := by have := M.qLarge; omega
  unfold Core.signFinish Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stageProduct_ok M (X.ready (M.context nq)) (M.scalarReady (by decide) nq)
    (by decide) (M.scalarFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  obtain E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.scalarFit (by decide)⟩)
  obtain U1 : operandValue s1 base (.local u) qLen = x * rv % q := by
    obtain V := R1.scalar_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [hx, hr] at V
    exact V
  obtain D1 := E1.buffer D (by decide)
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.prefix M1.saved nq (E1.prefixLen.trans hP)) M1 (D1.stream (M1.context nq)) D1.stack (by omega)
    (by decide) (M1.scalarFit (by decide))) fun s2 ⟨M2, R2⟩ => ?_)
  obtain E2 := R2.toStageFrame.execution (.inl ⟨by decide, M1.scalarFit (by decide)⟩)
  obtain E12 := E1.trans E2
  obtain Z2 : operandValue s2 base (.local z) qLen = digest % q := by
    obtain V := R2.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [E1.value D (by decide) M.extent, hD] at V
    exact V
  obtain U2 : operandValue s2 base (.local u) qLen = x * rv % q := by
    rw [R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide), U1]
  refine WP.seq (WP.mono (stageSum_ok M2 (M2.scalarReady (by decide) nq) (M2.scalarReady (by decide) nq)
    (by rw [Z2]; exact Nat.mod_lt _ qp) (by rw [U2]; exact Nat.mod_lt _ qp)
    (by decide) (M2.scalarFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  obtain E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.scalarFit (by decide)⟩)
  obtain E123 := E12.trans E3
  obtain V3 : operandValue s3 base (.local v) qLen = (digest % q + x * rv % q) % q := by
    obtain V := R3.scalar_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [Z2, U2] at V
    exact V
  obtain I3 : operandValue s3 base (.local VG.Impl.Dsa.Layout.inverse) qLen = inv := by
    rw [R3.toStageFrame.scalar_keep M2 (by decide) (by decide) (by decide),
      R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide),
      R1.toStageFrame.scalar_keep M (by decide) (by decide) (by decide), hi]
  refine WP.seq (WP.mono (stageProduct_ok M3 (M3.scalarReady (by decide) nq) (M3.scalarReady (by decide) nq)
    (by decide) (M3.scalarFit (by decide))) fun s4 ⟨M4, R4⟩ => ?_)
  refine WP.block_nil ⟨M4, ?_, ?_, ⟨E123.trans (R4.toStageFrame.execution (.inl ⟨by decide, M3.scalarFit (by decide)⟩)), ?_⟩⟩
  · rw [R4.toStageFrame.scalar_keep M3 (by decide) (by decide) (by decide),
      R3.toStageFrame.scalar_keep M2 (by decide) (by decide) (by decide),
      R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide),
      R1.toStageFrame.scalar_keep M (by decide) (by decide) (by decide), hr]
  · have V := R4.scalar_value M3 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [I3, V3] at V
    exact V

  · rw [R4.toStageFrame.mask_keep (by decide), R3.toStageFrame.mask_keep (by decide), R2.toStageFrame.mask_keep (by decide), R1.toStageFrame.mask_keep (by decide)]

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SignStart.lean`, which only this module imported.
section

/-! # The nonce power, reduced r, and Fermat inverse in signing -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signStart_ok {base : Addr} {size pLen qLen p q g k : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen) (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (hg : operandValue s0 base (.input .g) pLen = g) (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hq2 : operandValue s0 base (.local qMinusTwo) qLen = q - 2) :
    WP isa (Core.signStart pLen qLen) s0 fun s3 =>
      Moduli base size pLen qLen p q s3 ∧
      operandValue s3 base (.local r) qLen = g ^ k % p % q ∧
      operandValue s3 base (.local VG.Impl.Dsa.Layout.inverse) qLen = k ^ (q - 2) % q ∧
      Execution base s0 s3 ∧
      flagW base (Layout.field .mask) s3 = flagW base (Layout.field .mask) s0 := by
  have L := M.lengths
  have A := M.aligned
  obtain np : (pLen + 7) / 8 ≤ 48 := by omega
  obtain nq : (qLen + 7) / 8 ≤ 48 := by omega
  obtain qp : 0 < q := by have := M.qLarge; omega
  obtain pp : 0 < p := by have := M.pLarge; omega
  unfold Core.signStart Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stagePowerP_ok M (G.ready (M.context np)) (K.ready (M.context np))
    (by decide) (M.wideFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  obtain E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.wideFit (by decide)⟩)
  obtain V1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ k % p := by
    obtain V := R1.wide_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [hg, hk] at V
    exact V
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.imm _ _ _ _ _) M1 (M1.wideStream (by decide) nq) (M1.wideStack (by decide)) (by omega)
    (by decide) (M1.scalarFit (by decide))) fun s2 ⟨M2, R2⟩ => ?_)
  obtain E2 := R2.toStageFrame.execution (.inl ⟨by decide, M1.scalarFit (by decide)⟩)
  obtain E12 := E1.trans E2
  obtain V2 : operandValue s2 base (.local r) qLen = g ^ k % p % q := by
    obtain V := R2.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [V1] at V
    exact V
  obtain Q2 : operandValue s2 base (.local qMinusTwo) qLen = q - 2 := by
    rw [R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide),
      R1.toStageFrame.scalar_keep_wide M (by decide) (by decide), hq2]
  obtain K2 := E12.buffer K (by decide)
  obtain VK2 : operandValue s2 base (.input .nonce) qLen = k := (E12.value K (by decide) M.extent).trans hk
  refine WP.seq (WP.mono (stagePowerQ_ok M2 (K2.ready (M2.context nq))
    (M2.scalarReady (by decide) nq) (by decide) (M2.scalarFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  refine WP.block_nil ⟨M3, ?_, ?_, ⟨E12.trans (R3.toStageFrame.execution (.inl ⟨by decide, M2.scalarFit (by decide)⟩)), ?_⟩⟩
  · rw [R3.toStageFrame.scalar_keep M2 (by decide) (by decide) (by decide), V2]
  · have V := R3.scalar_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [VK2, Q2] at V
    exact V

  · rw [R3.toStageFrame.mask_keep (by decide), R2.toStageFrame.mask_keep (by decide), R1.toStageFrame.mask_keep (by decide)]

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/SignArithmetic.lean`, which only this module imported.
section

/-! # Complete arithmetic schedule of an x86 DSA signing attempt -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signArithmetic_ok {base : Addr} {size pLen qLen p q g k x digestLen digest : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hq2 : operandValue s0 base (.local qMinusTwo) qLen = q - 2) :
    WP isa (Core.sign pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local r) qLen = g ^ k % p % q ∧
      operandValue sf base (.local VG.Impl.Dsa.Layout.s) qLen =
        k ^ (q - 2) % q * ((digest % q + x * (g ^ k % p % q) % q) % q) % q ∧
      Execution base s0 sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 := by
  unfold Core.sign
  refine WP.seq (WP.mono (signStart_ok M G K hg hk hq2) fun s1 ⟨M1, R1, I1, E1, F1⟩ => ?_)
  refine WP.mono (signFinish_ok M1 (E1.buffer X (by decide)) (E1.buffer D (by decide)) hd (E1.prefixLen.trans hP)
    ((E1.value X (by decide) M.extent).trans hx)
    ((E1.value D (by decide) M.extent).trans hD) R1 I1) ?_
  intro sf H
  exact ⟨H.1, H.2.1, H.2.2.1, E1.trans H.2.2.2.1, H.2.2.2.2.trans F1⟩

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signCompute_ok {base : Addr} {size pLen qLen p q g y x k digestLen digest : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = digest) :
    let rv := g ^ k % p % q
    let sv := k ^ (q - 2) % q * ((digest % q + x * rv % q) % q) % q
    WP isa (SignVerify.signCompute pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local r) qLen = rv ∧
      operandValue sf base (.local VG.Impl.Dsa.Layout.s) qLen = sv ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&&
        mask32 (publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧
          g ^ x % p = y ∧ rv ≠ 0 ∧ sv ≠ 0) ∧ Execution base s0 sf := by
  dsimp only
  have L := M.lengths
  have A := M.aligned
  obtain nq : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  unfold SignVerify.signCompute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (publicKey_ok M G Y hg hy) fun s1 ⟨M1, F1, Q1, E1⟩ => ?_)
  refine WP.seq (WP.mono (privateKey_ok M1 (E1.buffer G (by decide)) (E1.buffer Y (by decide))
    (E1.buffer X (by decide)) (E1.buffer K (by decide))
    ((E1.value G (by decide) M.extent).trans hg) ((E1.value Y (by decide) M.extent).trans hy)
    ((E1.value X (by decide) M.extent).trans hx) ((E1.value K (by decide) M.extent).trans hk))
    fun s2 ⟨M2, F2, Q2, E2⟩ => ?_)
  obtain E12 := E1.trans E2
  refine WP.seq (WP.mono (signArithmetic_ok M2 (E12.buffer G (by decide)) (E12.buffer K (by decide))
    (E12.buffer X (by decide)) (E12.buffer D (by decide)) hd (E12.prefixLen.trans hP)
    ((E12.value G (by decide) M.extent).trans hg) ((E12.value K (by decide) M.extent).trans hk)
    ((E12.value X (by decide) M.extent).trans hx) ((E12.value D (by decide) M.extent).trans hD)
    (Q2.trans Q1)) fun s3 ⟨M3, R3, S3, E3, F3⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (stageZero_ok M3 (by omega_using [L]) (by omega_using [L]) (by omega_using [A])
    (M3.scalarReady (by decide) nq) true) fun s4 ⟨M4, F4, A4⟩ => ?_))
  obtain E4 := A4.execution (.inr ⟨rfl, rfl⟩)
  refine WP.mono (stageZero_ok M4 (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) (M4.scalarReady (by decide) nq) true)
    fun sf ⟨Mf, F5, A5⟩ => ?_
  refine WP.block_nil ⟨Mf, ?_, ?_, ?_, (((E12.trans E3).trans E4).trans (A5.execution (.inr ⟨rfl, rfl⟩)))⟩
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), R3]
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), S3]
  · rw [F5, F4, F3, F2, F1, A4.scalar_keep_mask M3 (by decide), R3, S3]
    simp only [ite_true, BitVec.and_assoc, mask32_and, and_assoc]

end VG.Proof.Dsa.X86

end

end

/-! # Constant-time verification arithmetic and validation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callVerifyScalars_relCT (L : CallLayout)
    (Q : CallOperand L (.input .q) L.qLen) (R : CallOperand L (.input .signature) L.qLen)
    (S : CallOperand L .signatureS L.qLen) (D : CallOperand L (.input .digest) L.digestPrefix)
    (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.verifyScalars L.qLen) (CallPair L) := by
  have W := L.lengths
  have E := CallOperand.localBuffer L qMinusTwo L.qLen (by decide) (by change 14912 + L.qLen ≤ 15712; omega_using [W])
  have I := CallOperand.localBuffer L inverse L.qLen (by decide) (by change 14784 + L.qLen ≤ 15712; omega_using [W])
  have Z := CallOperand.localBuffer L z L.qLen (by decide) (by change 14880 + L.qLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPowerQ_relCT L .signatureS (.local qMinusTwo) inverse Q S E (by decide) (by change 14784 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callReduce_relCT (hl := fun _ h => by cases h) L (.input .digest) Core.digestPrefix L.digestPrefix z (.inr ⟨_, rfl⟩)
      (fun _ R => R.prefixOperand) Q D hd (by decide) (by change 14880 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callProductQ_relCT L (.local z) (.local inverse) u Q Z I (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callProductQ_relCT L (.input .signature) (.local inverse) v Q R I (by decide) (by change 14848 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.block_nil (fun _ _ h => h)))))

theorem callVerifyPowers_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen) :
    RelCT isa (CallPair L) (Core.verifyPowers L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W])
  have V := CallOperand.localBuffer L v L.qLen (by decide) (by change 14848 + L.qLen ≤ 15712; omega_using [W])
  have T := CallOperand.localBuffer L t L.pLen (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W])
  have T2 := CallOperand.localBuffer L t2 L.pLen (by decide) (by change 15328 + L.pLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPowerP_relCT L (.input .g) (.local u) t P G U (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callPowerP_relCT L (.input .y) (.local v) t2 P Y V (by decide) (by change 15328 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callProductP_relCT L (.local t) (.local t2) t P T T2 (by decide) (by change 14944 + L.pLen ≤ 15712; omega_using [W]))
    (RelCT.seq (callReduce_relCT (hl := fun _ _ => by have := L.lengths; omega_using [W]) L (.local t) (.imm (BitVec.ofNat 32 L.pLen)) L.pLen u (.inl ⟨_, rfl⟩)
      (fun s _ => LenOperand.imm _ _ _ s _) Q T (by omega_using [W]) (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W]))
    (RelCT.block_nil (fun _ _ h => h)))))

theorem callVerify_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (R : CallOperand L (.input .signature) L.qLen) (S : CallOperand L .signatureS L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (Core.verify L.pLen L.qLen) (CallPair L) :=
  RelCT.seq (callVerifyScalars_relCT L Q R S D hd) (callVerifyPowers_relCT L P Q G Y)

theorem callVerifyCompute_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (R : CallOperand L (.input .signature) L.qLen) (S : CallOperand L .signatureS L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (SignVerify.verifyCompute L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W])
  exact RelCT.seq (callPublicKey_relCT L P Q G Y)
    (RelCT.seq (RelCT.seq (callRange_relCT L L.qLen .q (.input .signature) false Q R (by omega_using [W]) (by omega_using [W]) L.aligned.2)
      (callRange_relCT L L.qLen .q .signatureS false Q S (by omega_using [W]) (by omega_using [W]) L.aligned.2))
    (RelCT.seq (callVerify_relCT L P Q G Y R S D hd)
    (RelCT.seq (callEqual_relCT L L.qLen (.local u) (.input .signature) U R (by omega_using [W]) (by omega_using [W]) L.aligned.2)
    (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Dsa.X86
