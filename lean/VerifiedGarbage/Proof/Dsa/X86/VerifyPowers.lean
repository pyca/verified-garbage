module
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # The two powers and final reductions of x86 DSA verification -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem verifyPowers_ok {base : Addr} {size pLen qLen p q g y uv vv : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hu : operandValue s0 base (.local u) qLen = uv)
    (hv : operandValue s0 base (.local v) qLen = vv) :
    WP isa (Core.verifyPowers pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local u) qLen = (g ^ uv % p * (y ^ vv % p) % p) % q ∧
      Execution base s0 sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 := by
  have L := M.lengths
  have np : (pLen + 7) / 8 ≤ 48 := by omega
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  have qp : 0 < q := by have := M.qLarge; omega
  have pp : 0 < p := by have := M.pLarge; omega
  unfold Core.verifyPowers Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stagePowerP_ok M (G.ready (M.context np)) (M.scalarReady (by decide) np)
    (by decide) (M.wideFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.wideFit (by decide)⟩)
  have T1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ uv % p := by
    have V := R1.wide_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [hg, hu] at V
    exact V
  have V1 : operandValue s1 base (.local v) qLen = vv := by
    rw [R1.toStageFrame.scalar_keep_wide M (by decide) (by decide), hv]
  have Y1 := E1.buffer Y (by decide)
  refine WP.seq (WP.mono (stagePowerP_ok M1 (Y1.ready (M1.context np)) (M1.scalarReady (by decide) np)
    (by decide) (M1.wideFit (by decide))) fun s2 ⟨M2, R2⟩ => ?_)
  have E2 := R2.toStageFrame.execution (.inl ⟨by decide, M1.wideFit (by decide)⟩)
  have E12 := E1.trans E2
  have T2 : operandValue s2 base (.local t2) pLen = y ^ vv % p := by
    have V := R2.wide_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [E1.value Y (by decide) M.extent, hy, V1] at V
    exact V
  have T12 : operandValue s2 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ uv % p := by
    rw [R2.toStageFrame.wide_keep M1 (by decide) (by decide) (by decide), T1]
  refine WP.seq (WP.mono (stageProductP_ok M2 (M2.wideReady (by decide) np) (M2.wideReady (by decide) np)
    (by decide) (M2.wideFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.wideFit (by decide)⟩)
  have T3 : operandValue s3 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ uv % p * (y ^ vv % p) % p := by
    have V := R3.wide_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [T12, T2] at V
    exact V
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.imm _ _ _ _ _) M3 (M3.wideStream (by decide) nq) (M3.wideStack (by decide)) (by omega)
    (by decide) (M3.scalarFit (by decide))) fun sf ⟨Mf, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, ⟨(E12.trans E3).trans (R4.toStageFrame.execution (.inl ⟨by decide, M3.scalarFit (by decide)⟩)), ?_⟩⟩
  · have V := R4.scalar_value M3 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [T3] at V
    exact V
  · rw [R4.toStageFrame.mask_keep (by decide), R3.toStageFrame.mask_keep (by decide), R2.toStageFrame.mask_keep (by decide), R1.toStageFrame.mask_keep (by decide)]


end VG.Proof.Dsa.X86
