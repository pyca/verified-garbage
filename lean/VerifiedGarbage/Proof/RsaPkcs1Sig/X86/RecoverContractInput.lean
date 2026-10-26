module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverContractGeometry
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverFnInput
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverABI
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverEntryReady
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRegions
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Weierstrass
import Mathlib.Tactic.ToDual

/-! # Decode the shared verifier precondition into its frame and input geometry -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem recover_contract_pre (s : State) (pre : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s) :
    FnInput (recoverGeometry s) (recoverBytes s) s := by
  have h := recoverABI_of pre
  have fits : ∀ i, ((recoverGeometry s).sources i).toNat + (recoverGeometry s).sourceLength i ≤ 2 ^ 32 := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    exacts [h.sourceFit0, h.sourceFit1, h.sourceFit2, h.sourceFit3]
  have geometry : (recoverGeometry s).Valid := by
    refine ⟨h.valid.1, h.valid.2, h.ePositive, h.eFits, h.hash, (arg s 8).isLt,
      h.preLength, h.space, ?_, ?_, h.outputFit, ?_, h.outputWorkspace, ?_, ?_, fits,
      h.workspaceFit, ?_, ?_, ?_, ?_, ?_⟩
    · rw [recoverGeometry_stackNat s h.stackLow]
      have := h.stackLow
      simp only [recoverStack] at this
      omega
    · rw [recoverGeometry_stackNat s h.stackLow]
      have := h.stackBound
      simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]
      omega
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
      exacts [h.outputSource0, h.outputSource1, h.outputSource2, h.outputSource3]
    · rw [recoverGeometry_arguments s h.stackLow h.stackBound]; exact h.outputArguments
    · rw [recoverGeometry_wholeStack s h.stackLow]; exact h.stackOutput
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
      exacts [h.sourceWorkspace0, h.sourceWorkspace1, h.sourceWorkspace2, h.sourceWorkspace3]
    · rw [recoverGeometry_arguments s h.stackLow h.stackBound]; exact h.workspaceArguments
    · intro i
      rw [recoverGeometry_wholeStack s h.stackLow]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
      exacts [h.stackSource0, h.stackSource1, h.stackSource2, h.stackSource3]
    · rw [recoverGeometry_wholeStack s h.stackLow]; exact h.stackWorkspace
    · rw [recoverGeometry_wholeStack s h.stackLow, recoverGeometry_arguments s h.stackLow h.stackBound]
      exact h.stackArguments
  apply EntryInput.ready
  refine ⟨geometry, h.stackLow, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨fits i, ?_, rfl⟩
    refine ⟨(recoverGeometry s).sourceRegion i, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    rw [h.rd]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [h.wr]
    exact ⟨_, by simp [recoverGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [h.wr]
    exact ⟨_, by simp [recoverGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [recoverGeometry_arguments s h.stackLow h.stackBound]
    exact ⟨_, List.mem_append_right _ (by rw [h.wr]; simp), Region.contains_self _ _⟩
  · intro j hj
    have address : byteAddr (recoverGeometry s).stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j) = argAddr s j := by
      rw [← Offset.add_add]
      change (recoverGeometry s).argumentsRegion.base + BitVec.ofNat 64 (4 * j) = _
      rw [recoverGeometry_arguments s h.stackLow h.stackBound]
      simp only [argAddr, Nat.mul_zero, Nat.add_zero]
      have bound := h.stackBound
      have first := byteAddr_add (by omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
      have last := byteAddr_add (by omega : (s.gpr .esp).toNat + (4 + 4 * j) < 2 ^ 32)
      change byteAddr (s.gpr .esp + BitVec.ofNat 32 4) + BitVec.ofNat 64 (4 * j) = byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j))
      rw [first, last, Offset.add_add]
    rw [address]
    change arg s j = _
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [recoverGeometry, Geometry.argument, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    all_goals rfl
  · intro r hr
    have belowRet : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (recoverGeometry s).wholeStack := by
      rw [recoverGeometry_wholeStack s h.stackLow]
      have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack)
        (Nat.le_refl recoverStack) (by decide : recoverStack + 4 ≤ 2 ^ 64)
      rw [BitVec.sub_add_cancel] at sep
      exact sep
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact belowRet.sub_right geometry.innerSub
    · exact belowRet.sub_right geometry.calleeSub
    · exact h.returnOutput
    · exact h.returnWorkspace

end VG.Proof.RsaPkcs1Sig.X86.Rcv
