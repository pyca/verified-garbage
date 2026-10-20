module
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # Both public components satisfy their subgroup-power checks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem subgroup_ok {base : Addr} {size pLen qLen p q g y : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y) :
    WP isa (Validate.subgroup pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf =
        (flagW base (Layout.field .mask) s0 &&& mask32 (g ^ q % p = 1)) &&& mask32 (y ^ q % p = 1) ∧
      operandValue sf base (.local qMinusTwo) qLen = operandValue s0 base (.local qMinusTwo) qLen ∧
      Execution base s0 sf := by
  have L := M.lengths
  have A := M.aligned
  have np : (pLen + 7) / 8 ≤ 48 := by omega
  have pp : 0 < p := by have := M.pLarge; omega
  unfold Validate.subgroup Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stagePowerP_ok M (G.ready (M.context np)) (M.qBuffer.ready (M.context np))
    (by decide) (M.wideFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.wideFit (by decide)⟩)
  have T1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ q % p := by
    have V := R1.wide_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [hg, M.qValue] at V
    exact V
  refine WP.seq (WP.mono (stageOne_ok M1 (by omega) (by omega) (by omega) (M1.wideReady (by decide) np))
    fun s2 ⟨M2, F2, R2⟩ => ?_)
  have E2 := R2.execution (.inr ⟨rfl, rfl⟩)
  have E12 := E1.trans E2
  have Y2 := E12.buffer Y (by decide)
  refine WP.seq (WP.mono (stagePowerP_ok M2 (Y2.ready (M2.context np)) (M2.qBuffer.ready (M2.context np))
    (by decide) (M2.wideFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.wideFit (by decide)⟩)
  have T3 : operandValue s3 base (.local VG.Impl.Dsa.Layout.t) pLen = y ^ q % p := by
    have V := R3.wide_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [E12.value Y (by decide) M.extent, hy, M2.qValue] at V
    exact V
  refine WP.seq (WP.mono (stageOne_ok M3 (by omega) (by omega) (by omega) (M3.wideReady (by decide) np))
    fun sf ⟨Mf, F4, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, ?_, (E12.trans E3).trans (R4.execution (.inr ⟨rfl, rfl⟩))⟩
  · rw [F4, R3.toStageFrame.mask_keep (by decide), F2, R1.toStageFrame.mask_keep (by decide), T1, T3]
  · rw [R4.scalar_keep_mask M3 (by decide), R3.toStageFrame.scalar_keep_wide M2 (by decide) (by decide),
      R2.scalar_keep_mask M1 (by decide), R1.toStageFrame.scalar_keep_wide M (by decide) (by decide)]

end VG.Proof.Dsa.X86
