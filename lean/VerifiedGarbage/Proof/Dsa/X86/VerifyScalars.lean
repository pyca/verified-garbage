module
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # The inverse and scalar exponents of x86 DSA verification -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem verifyScalars_ok {base : Addr} {size pLen qLen p q digestLen digest rv sv : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (R : CallerBuffer s0 base size (.input .signature) qLen)
    (S : CallerBuffer s0 base size .signatureS qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hr : operandValue s0 base (.input .signature) qLen = rv)
    (hs : operandValue s0 base .signatureS qLen = sv)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hq2 : operandValue s0 base (.local qMinusTwo) qLen = q - 2) :
    WP isa (Core.verifyScalars qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local u) qLen = digest % q * (sv ^ (q - 2) % q) % q ∧
      operandValue sf base (.local v) qLen = rv * (sv ^ (q - 2) % q) % q ∧
      Execution base s0 sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 := by
  have L := M.lengths
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  have qp : 0 < q := by have := M.qLarge; omega
  unfold Core.verifyScalars Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stagePowerQ_ok M (S.ready (M.context nq)) (M.scalarReady (by decide) nq)
    (by decide) (M.scalarFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.scalarFit (by decide)⟩)
  have I1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.inverse) qLen = sv ^ (q - 2) % q := by
    have V := R1.scalar_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [hs, hq2] at V
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
  have I2 : operandValue s2 base (.local VG.Impl.Dsa.Layout.inverse) qLen = sv ^ (q - 2) % q := by
    rw [R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide), I1]
  refine WP.seq (WP.mono (stageProduct_ok M2 (M2.scalarReady (by decide) nq) (M2.scalarReady (by decide) nq)
    (by decide) (M2.scalarFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.scalarFit (by decide)⟩)
  have E123 := E12.trans E3
  have U3 : operandValue s3 base (.local u) qLen = digest % q * (sv ^ (q - 2) % q) % q := by
    have V := R3.scalar_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [Z2, I2] at V
    exact V
  have I3 : operandValue s3 base (.local VG.Impl.Dsa.Layout.inverse) qLen = sv ^ (q - 2) % q := by
    rw [R3.toStageFrame.scalar_keep M2 (by decide) (by decide) (by decide), I2]
  have Rbuf := E123.buffer R (by decide)
  refine WP.seq (WP.mono (stageProduct_ok M3 (Rbuf.ready (M3.context nq)) (M3.scalarReady (by decide) nq)
    (by decide) (M3.scalarFit (by decide))) fun sf ⟨Mf, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, ?_, ⟨E123.trans (R4.toStageFrame.execution (.inl ⟨by decide, M3.scalarFit (by decide)⟩)), ?_⟩⟩
  · rw [R4.toStageFrame.scalar_keep M3 (by decide) (by decide) (by decide), U3]
  · have V := R4.scalar_value M3 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [E123.value R (by decide) M.extent, hr, I3] at V
    exact V

  · rw [R4.toStageFrame.mask_keep (by decide), R3.toStageFrame.mask_keep (by decide), R2.toStageFrame.mask_keep (by decide), R1.toStageFrame.mask_keep (by decide)]

end VG.Proof.Dsa.X86
