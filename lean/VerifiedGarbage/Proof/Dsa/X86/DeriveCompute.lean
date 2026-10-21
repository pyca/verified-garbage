module

import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.StageValues
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters

/-! # Derivation computes y and accumulates the private and public ranges -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem stageWide_keep_mask {base : Addr} {size pLen qLen p q d : Nat} {s t : State}
    (F : StageFrame base s t (Layout.field .mask) 4) (M : Moduli base size pLen qLen p q s)
    (hd : d ∈ Layout.wideValues) :
    operandValue t base (.local d) pLen = operandValue s base (.local d) pLen := by
  have H := VG.Proof.Dsa.X86.Layout.wide_bounds hd
  exact F.local_value_keep M.scr (by have := M.lengths; omega)
    (by change 7048 ≤ d; omega) (Nat.le_trans (M.wideFit hd) M.extent)
    (by have Hs : 8256 ≤ size := M.saved; change 8248 ≤ size; omega) (M.wideFit hd)
    (.inr (by change 8248 ≤ d; omega))

theorem deriveCompute_ok {base : Addr} {size pLen qLen p q g x : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (X : CallerBuffer s0 base size (.input .nonce) qLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hx : operandValue s0 base (.input .nonce) qLen = x) :
    WP isa (Generate.deriveCompute pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&&
        mask32 (((1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1) ∧
          (0 < x ∧ x < q) ∧ (1 < g ^ x % p ∧ g ^ x % p < p)) ∧
      operandValue sf base (.local t2) pLen = g ^ x % p ∧
      Execution base s0 sf := by
  have L := M.lengths
  have A := M.aligned
  have np : (pLen + 7) / 8 ≤ 48 := by omega
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  have pp : 0 < p := by have := M.pLarge; omega
  unfold Generate.deriveCompute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (generateParameters_ok M G hg) fun s1 ⟨M1, F1, E1⟩ => ?_)
  have X1 := E1.buffer X (by decide)
  refine WP.seq (WP.mono (stageRange_ok M1 (by omega) (by omega) (by omega)
    M1.qReady (X1.ready (M1.context nq)) false) fun s2 ⟨M2, F2, R2⟩ => ?_)
  have E2 := R2.execution (.inr ⟨rfl, rfl⟩)
  have E12 := E1.trans E2
  refine WP.seq (WP.mono (stagePowerP_ok M2
    ((E12.buffer G (by decide)).ready (M2.context np))
    ((E12.buffer X (by decide)).ready (M2.context np))
    (by decide) (M2.wideFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.wideFit (by decide)⟩)
  have Y3 : operandValue s3 base (.local t2) pLen = g ^ x % p := by
    have V := R3.wide_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [E12.value G (by decide) M.extent, E12.value X (by decide) M.extent, hg, hx] at V
    exact V
  refine WP.seq (WP.mono (stageRange_ok M3 (by omega) (by omega) (by omega)
    M3.pReady (M3.wideReady (by decide) np) true) fun sf ⟨Mf, F4, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, (stageWide_keep_mask R4 M3 (by decide)).trans Y3,
    (E12.trans E3).trans (R4.execution (.inr ⟨rfl, rfl⟩))⟩
  rw [F4, R3.toStageFrame.mask_keep (by decide), F2, F1, Y3,
    E1.value X (by decide) M.extent, hx, M1.qValue, M3.pValue]
  simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.and_assoc, mask32_and, and_assoc]

end VG.Proof.Dsa.X86
