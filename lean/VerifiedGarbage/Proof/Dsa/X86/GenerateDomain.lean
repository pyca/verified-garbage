module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.StageMinus
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # Generation checks the generator's range and q divides p-1 -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem generateDomain_ok {base : Addr} {size pLen qLen p q g : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (hg : operandValue s0 base (.input .g) pLen = g) :
    WP isa (Generate.domain pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf =
        (flagW base (Layout.field .mask) s0 &&& mask32 (1 < g ∧ g < p)) &&&
          mask32 ((p - 1) % q = 0) ∧ Execution base s0 sf := by
  have L := M.lengths
  have A := M.aligned
  have np : (pLen + 7) / 8 ≤ 48 := by omega
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  have qp : 0 < q := by have := M.qLarge; omega
  unfold Generate.domain Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono
    (stageRange_ok M (by omega) (by omega) (by omega) M.pReady (G.ready (M.context np)) true)
    fun s1 ⟨M1, F1, R1⟩ => ?_)
  have E1 := R1.execution (.inr ⟨rfl, rfl⟩)
  refine WP.seq (WP.mono (stageMinusP_ok M1 (by have := M.pLarge; omega)
    (by decide) (M1.wideFit (by decide))) fun s2 ⟨M2, R2⟩ => ?_)
  have E2 := R2.toStageFrame.execution (.inl ⟨by decide, M1.wideFit (by decide)⟩)
  have T2 : operandValue s2 base (.local VG.Impl.Dsa.Layout.t) pLen = p - 1 :=
    R2.wide_value M1 (by decide) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) M.valueBounds.1)
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.imm _ _ _ _ _) M2 (M2.wideStream (by decide) nq) (M2.wideStack (by decide)) (by omega)
    (by decide) (M2.scalarFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.scalarFit (by decide)⟩)
  have U3 : operandValue s3 base (.local u) qLen = (p - 1) % q := by
    have V := R3.scalar_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [T2] at V
    exact V
  refine WP.seq (WP.mono (stageZero_ok M3 (by omega) (by omega) (by omega)
    (M3.scalarReady (by decide) nq) false) fun sf ⟨Mf, F4, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, ((E1.trans E2).trans E3).trans
    (R4.execution (.inr ⟨rfl, rfl⟩))⟩
  rw [F4, R3.toStageFrame.mask_keep (by decide), R2.toStageFrame.mask_keep (by decide),
    F1, U3, hg, M.pValue]
  rfl

end VG.Proof.Dsa.X86
