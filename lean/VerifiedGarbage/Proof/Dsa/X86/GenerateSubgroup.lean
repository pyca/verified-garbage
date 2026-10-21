module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli

import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # Generation's single subgroup power -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem generateSubgroup_ok {base : Addr} {size pLen qLen p q g : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (hg : operandValue s0 base (.input .g) pLen = g) :
    WP isa (Generate.subgroup pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf =
        flagW base (Layout.field .mask) s0 &&& mask32 (g ^ q % p = 1) ∧
      Execution base s0 sf := by
  have L := M.lengths
  have A := M.aligned
  have np : (pLen + 7) / 8 ≤ 48 := by omega
  have pp : 0 < p := by have := M.pLarge; omega
  unfold Generate.subgroup Generate.subgroupWith
  refine WP.seq (WP.mono (stagePowerP_ok M (G.ready (M.context np)) (M.qBuffer.ready (M.context np))
    (by decide) (M.wideFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.wideFit (by decide)⟩)
  have T1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ q % p := by
    have V := R1.wide_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [hg, M.qValue] at V
    exact V
  refine WP.mono (stageOne_ok M1 (by omega) (by omega) (by omega)
    (M1.wideReady (by decide) np)) fun sf ⟨Mf, F2, R2⟩ => ?_
  refine ⟨Mf, ?_, E1.trans (R2.execution (.inr ⟨rfl, rfl⟩))⟩
  rw [F2, R1.toStageFrame.mask_keep (by decide), T1]

end VG.Proof.Dsa.X86
