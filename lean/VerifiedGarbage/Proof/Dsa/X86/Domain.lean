module
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.StageMinus
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # Public component ranges and divisibility checks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem domain_ok {base : Addr} {size pLen qLen p q g y : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y) :
    WP isa (Validate.domain pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf =
        ((flagW base (Layout.field .mask) s0 &&& mask32 (1 < g ∧ g < p)) &&&
          mask32 (1 < y ∧ y < p)) &&& mask32 ((p - 1) % q = 0) ∧
      operandValue sf base (.local qMinusTwo) qLen = q - 2 ∧ Execution base s0 sf := by
  have L := M.lengths
  have A := M.aligned
  have np : (pLen + 7) / 8 ≤ 48 := by omega
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  have qp : 0 < q := by have := M.qLarge; omega
  unfold Validate.domain Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.seq (WP.mono
    (stageRange_ok M (by omega) (by omega) (by omega) M.pReady (G.ready (M.context np)) true)
    fun s1 ⟨M1, F1, R1⟩ => ?_))
  have E1 := R1.execution (.inr ⟨rfl, rfl⟩)
  have Y1 := E1.buffer Y (by decide)
  refine WP.mono (stageRange_ok M1 (by omega) (by omega) (by omega) M1.pReady (Y1.ready (M1.context np)) true)
    fun s2 ⟨M2, F2, R2⟩ => ?_
  have E2 := R2.execution (.inr ⟨rfl, rfl⟩)
  have E12 := E1.trans E2
  refine WP.seq (WP.mono (stageMinusP_ok M2 (by have := M.pLarge; omega)
    (by decide) (M2.wideFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.wideFit (by decide)⟩)
  have T3 : operandValue s3 base (.local VG.Impl.Dsa.Layout.t) pLen = p - 1 :=
    R3.wide_value M2 (by decide) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) M.valueBounds.1)
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.imm _ _ _ _ _) M3 (M3.wideStream (by decide) nq) (by omega)
    (by decide) (M3.scalarFit (by decide))) fun s4 ⟨M4, R4⟩ => ?_)
  have E4 := R4.toStageFrame.execution (.inl ⟨by decide, M3.scalarFit (by decide)⟩)
  have U4 : operandValue s4 base (.local u) qLen = (p - 1) % q := by
    have V := R4.scalar_value M3 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [T3] at V
    exact V
  refine WP.seq (WP.mono (stageZero_ok M4 (by omega) (by omega) (by omega) (M4.scalarReady (by decide) nq) false)
    fun s5 ⟨M5, F5, R5⟩ => ?_)
  have E5 := R5.execution (.inr ⟨rfl, rfl⟩)
  refine WP.seq (WP.mono (stageMinusQ_ok M5 (by have := M.qLarge; omega)
    (by decide) (M5.scalarFit (by decide))) fun sf ⟨Mf, R6⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, ?_, ((((E12.trans E3).trans E4).trans E5).trans
    (R6.toStageFrame.execution (.inl ⟨by decide, M5.scalarFit (by decide)⟩)))⟩
  · rw [R6.toStageFrame.mask_keep (by decide), F5, R4.toStageFrame.mask_keep (by decide),
      R3.toStageFrame.mask_keep (by decide), F2, F1, U4,
      E1.value Y (by decide) M.extent, hg, hy, M.pValue, M1.pValue]
    rfl
  · exact R6.scalar_value M5 (by decide) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) M.valueBounds.2)

end VG.Proof.Dsa.X86
