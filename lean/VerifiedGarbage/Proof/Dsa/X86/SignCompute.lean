module

public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.PublicKey
import VerifiedGarbage.Proof.Dsa.X86.PrivateKey
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StagePower
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
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  have qp : 0 < q := by have := M.qLarge; omega
  unfold Core.signFinish Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stageProduct_ok M (X.ready (M.context nq)) (M.scalarReady (by decide) nq)
    (by decide) (M.scalarFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.scalarFit (by decide)⟩)
  have U1 : operandValue s1 base (.local u) qLen = x * rv % q := by
    have V := R1.scalar_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [hx, hr] at V
    exact V
  have D1 := E1.buffer D (by decide)
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.prefix M1.saved nq (E1.prefixLen.trans hP)) M1 (D1.stream (M1.context nq)) D1.stack (by omega)
    (by decide) (M1.scalarFit (by decide))) fun s2 ⟨M2, R2⟩ => ?_)
  have E2 := R2.toStageFrame.execution (.inl ⟨by decide, M1.scalarFit (by decide)⟩)
  have E12 := E1.trans E2
  have Z2 : operandValue s2 base (.local z) qLen = digest % q := by
    have V := R2.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [E1.value D (by decide) M.extent, hD] at V
    exact V
  have U2 : operandValue s2 base (.local u) qLen = x * rv % q := by
    rw [R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide), U1]
  refine WP.seq (WP.mono (stageSum_ok M2 (M2.scalarReady (by decide) nq) (M2.scalarReady (by decide) nq)
    (by rw [Z2]; exact Nat.mod_lt _ qp) (by rw [U2]; exact Nat.mod_lt _ qp)
    (by decide) (M2.scalarFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.scalarFit (by decide)⟩)
  have E123 := E12.trans E3
  have V3 : operandValue s3 base (.local v) qLen = (digest % q + x * rv % q) % q := by
    have V := R3.scalar_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [Z2, U2] at V
    exact V
  have I3 : operandValue s3 base (.local VG.Impl.Dsa.Layout.inverse) qLen = inv := by
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
  have np : (pLen + 7) / 8 ≤ 48 := by omega
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  have qp : 0 < q := by have := M.qLarge; omega
  have pp : 0 < p := by have := M.pLarge; omega
  unfold Core.signStart Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stagePowerP_ok M (G.ready (M.context np)) (K.ready (M.context np))
    (by decide) (M.wideFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.wideFit (by decide)⟩)
  have V1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ k % p := by
    have V := R1.wide_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [hg, hk] at V
    exact V
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.imm _ _ _ _ _) M1 (M1.wideStream (by decide) nq) (M1.wideStack (by decide)) (by omega)
    (by decide) (M1.scalarFit (by decide))) fun s2 ⟨M2, R2⟩ => ?_)
  have E2 := R2.toStageFrame.execution (.inl ⟨by decide, M1.scalarFit (by decide)⟩)
  have E12 := E1.trans E2
  have V2 : operandValue s2 base (.local r) qLen = g ^ k % p % q := by
    have V := R2.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [V1] at V
    exact V
  have Q2 : operandValue s2 base (.local qMinusTwo) qLen = q - 2 := by
    rw [R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide),
      R1.toStageFrame.scalar_keep_wide M (by decide) (by decide), hq2]
  have K2 := E12.buffer K (by decide)
  have VK2 : operandValue s2 base (.input .nonce) qLen = k := (E12.value K (by decide) M.extent).trans hk
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

section
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
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  unfold SignVerify.signCompute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (publicKey_ok M G Y hg hy) fun s1 ⟨M1, F1, Q1, E1⟩ => ?_)
  refine WP.seq (WP.mono (privateKey_ok M1 (E1.buffer G (by decide)) (E1.buffer Y (by decide))
    (E1.buffer X (by decide)) (E1.buffer K (by decide))
    ((E1.value G (by decide) M.extent).trans hg) ((E1.value Y (by decide) M.extent).trans hy)
    ((E1.value X (by decide) M.extent).trans hx) ((E1.value K (by decide) M.extent).trans hk))
    fun s2 ⟨M2, F2, Q2, E2⟩ => ?_)
  have E12 := E1.trans E2
  refine WP.seq (WP.mono (signArithmetic_ok M2 (E12.buffer G (by decide)) (E12.buffer K (by decide))
    (E12.buffer X (by decide)) (E12.buffer D (by decide)) hd (E12.prefixLen.trans hP)
    ((E12.value G (by decide) M.extent).trans hg) ((E12.value K (by decide) M.extent).trans hk)
    ((E12.value X (by decide) M.extent).trans hx) ((E12.value D (by decide) M.extent).trans hD)
    (Q2.trans Q1)) fun s3 ⟨M3, R3, S3, E3, F3⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (stageZero_ok M3 (by omega) (by omega) (by omega)
    (M3.scalarReady (by decide) nq) true) fun s4 ⟨M4, F4, A4⟩ => ?_))
  have E4 := A4.execution (.inr ⟨rfl, rfl⟩)
  refine WP.mono (stageZero_ok M4 (by omega) (by omega) (by omega) (M4.scalarReady (by decide) nq) true)
    fun sf ⟨Mf, F5, A5⟩ => ?_
  refine WP.block_nil ⟨Mf, ?_, ?_, ?_, (((E12.trans E3).trans E4).trans (A5.execution (.inr ⟨rfl, rfl⟩)))⟩
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), R3]
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), S3]
  · rw [F5, F4, F3, F2, F1, A4.scalar_keep_mask M3 (by decide), R3, S3]
    simp only [ite_true, BitVec.and_assoc, mask32_and, and_assoc]

end VG.Proof.Dsa.X86
