module
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # Private-key, nonce-range, and public-key consistency checks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem privateKey_ok {base : Addr} {size pLen qLen p q g y x k : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k) :
    WP isa (Validate.privateKey pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf =
        ((flagW base (Layout.field .mask) s0 &&& mask32 (0 < x ∧ x < q)) &&&
          mask32 (0 < k ∧ k < q)) &&& mask32 (g ^ x % p = y) ∧
      operandValue sf base (.local qMinusTwo) qLen = operandValue s0 base (.local qMinusTwo) qLen ∧
      Execution base s0 sf := by
  have L := M.lengths
  have A := M.aligned
  have np : (pLen + 7) / 8 ≤ 48 := by omega
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  have pp : 0 < p := by have := M.pLarge; omega
  unfold Validate.privateKey Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.seq (WP.mono
    (stageRange_ok M (by omega) (by omega) (by omega) M.qReady (X.ready (M.context nq)) false)
    fun s1 ⟨M1, F1, R1⟩ => ?_))
  have E1 := R1.execution (.inr ⟨rfl, rfl⟩)
  have K1 := E1.buffer K (by decide)
  refine WP.mono (stageRange_ok M1 (by omega) (by omega) (by omega) M1.qReady (K1.ready (M1.context nq)) false)
    fun s2 ⟨M2, F2, R2⟩ => ?_
  have E2 := R2.execution (.inr ⟨rfl, rfl⟩)
  have E12 := E1.trans E2
  have G2 := E12.buffer G (by decide)
  have X2 := E12.buffer X (by decide)
  refine WP.seq (WP.mono (stagePowerP_ok M2 (G2.ready (M2.context np)) (X2.ready (M2.context np))
    (by decide) (M2.wideFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.wideFit (by decide)⟩)
  have E123 := E12.trans E3
  have T3 : operandValue s3 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ x % p := by
    have V := R3.wide_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [E12.value G (by decide) M.extent, E12.value X (by decide) M.extent, hg, hx] at V
    exact V
  have Y3 := E123.buffer Y (by decide)
  refine WP.seq (WP.mono (stageEqual_ok M3 (by omega) (by omega) (by omega) (M3.wideReady (by decide) np)
    (Y3.ready (M3.context np))) fun sf ⟨Mf, F4, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, ?_, E123.trans (R4.execution (.inr ⟨rfl, rfl⟩))⟩
  · rw [F4, R3.toStageFrame.mask_keep (by decide), F2, F1, T3,
      E123.value Y (by decide) M.extent, E1.value K (by decide) M.extent, hy, hk, hx, M.qValue, M1.qValue]
    rfl
  · rw [R4.scalar_keep_mask M3 (by decide), R3.toStageFrame.scalar_keep_wide M2 (by decide) (by decide),
      R2.scalar_keep_mask M1 (by decide), R1.scalar_keep_mask M (by decide)]

end VG.Proof.Dsa.X86
