module

import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.Persistent
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

/-! # The nonce power, reduced r, and Fermat inverse in signing -/

@[expose] public section
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
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.imm _ _ _ _ _) M1 (M1.wideStream (by decide) nq) (by omega)
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
