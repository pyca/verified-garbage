module

import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.StageValues
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.ValidateRange
import VerifiedGarbage.Proof.Dsa.X86.DeriveCompute
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags

/-! # Derivation computes y and accumulates the private and public ranges -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Comb
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem deriveCompute_ok {base : Addr} {size pLen qLen p q g x : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (X : CallerBuffer s0 base size (.input .nonce) qLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hx : operandValue s0 base (.input .nonce) qLen = x)
    (domain : (1<g ∧ g<p) ∧ (p-1)%q=0 ∧ g^q%p=1)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size)
    (C : canonical ((pLen+7)/8) ((qLen+3)/4) p g base s0.mem) :
    WP isa (deriveCompute pLen qLen) s0 fun sf =>
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
  unfold deriveCompute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (validateRange_ok M.scr M.saved rfl (by omega) (by omega) A.2
    M.qReady (X.ready (M.context nq)) false) fun s2 ⟨F2,K2,O2⟩ => ?_)
  have R2 := StageFrame.of_frame K2 (by decide) O2 nq
  have E12 := R2.execution (.inr ⟨rfl,rfl⟩)
  have M2 := M.keep E12.mem E12.keeps (by decide) (by decide)
  have C2 := canonical_check (supported_widths M.widths) nq C O2
  refine WP.seq (WP.mono (stagePrivate_ok M2
    ((E12.buffer G (by decide)).ready (M2.context np))
    ((E12.buffer X (by decide)).ready (M2.context np))
    (by decide) sizeComb (by rw [E12.value G (by decide) M.extent,hg]; exact C2)) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.wideFit (by decide)⟩)
  have Y3 : operandValue s3 base (.local t2) pLen = g ^ x % p := by
    have V := R3.wide_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [E12.value G (by decide) M.extent, E12.value X (by decide) M.extent, hg, hx] at V
    exact V
  refine WP.seq (WP.mono (stageRange_ok M3 (by omega) (by omega) (by omega)
    M3.pReady (M3.wideReady (by decide) np) true) fun sf ⟨Mf, F4, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, (stageWide_keep_mask R4 M3 (by decide)).trans Y3,
    (E12.trans E3).trans (R4.execution (.inr ⟨rfl, rfl⟩))⟩
  have qValue := M.qValue
  unfold operandValue at hx qValue
  rw [F4, R3.toStageFrame.mask_keep (by decide), F2, Y3, hx, qValue, M3.pValue]
  simp only [domain, true_and]
  simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.and_assoc, mask32_and, and_assoc]

end VG.Proof.Dsa.X86.Comb
