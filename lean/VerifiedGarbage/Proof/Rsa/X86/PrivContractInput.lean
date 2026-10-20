module
public import VerifiedGarbage.Proof.Rsa.X86.PrivContractGeometry
public import VerifiedGarbage.Proof.Rsa.X86.PrivFnInput

import VerifiedGarbage.Proof.Rsa.X86.PrivABI
import VerifiedGarbage.Proof.Rsa.X86.PrivEntryReady
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Weierstrass

/-! # Shared private RSA preconditions establish the i686 wrapper inputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem private_contract_pre (s : State) (h : (Spec.Rsa.privateCheckedContract abi stackBytes).pre s) :
    PrivFnInput (privateGeometry s) (privateBytes s) s := by
  obtain ⟨stackFit, argFit, rd, wr, outN, outE, outI, outP, outQ, outDP, outDQ, outQI, outWs, outArgs,
    nWs, eWs, iWs, pWs, qWs, dpWs, dqWs, qiWs, wsArgs,
    stackOut, stackN, stackE, stackI, stackP, stackQ, stackDP, stackDQ, stackQI, stackWs, stackArgs,
    retOut, retWs, outFit, nFit, eFit, iFit, pFit, qFit, dpFit, dqFit, qiFit, wsFit,
    valid, outLen, inputLen, ePositive, eFits, pPositive, pShort, qPositive, qShort, dpLen, qiLen, dqLen, space⟩ := privateABI_of h
  rw [outLen] at wr outN outE outI outP outQ outDP outDQ outQI outWs outArgs stackOut outFit retOut
  rw [inputLen] at rd outI iWs stackI iFit
  rw [dpLen] at rd outDP dpWs stackDP dpFit
  rw [dqLen] at rd outDQ dqWs stackDQ dqFit
  rw [qiLen] at rd outQI qiWs stackQI qiFit
  rw [show (arg s 19).toNat * 8 = 8 * (arg s 19).toNat from Nat.mul_comm _ _]
    at wr outWs nWs eWs iWs pWs qWs dpWs dqWs qiWs wsArgs stackWs wsFit retWs
  have sourceFit : ∀ i, ((privateGeometry s).sources i).toNat + (privateGeometry s).sourceLength i ≤ 2 ^ 32 := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [nFit, eFit, iFit, pFit, qFit, dpFit, dqFit, qiFit]
  have geometry : (privateGeometry s).Valid := by
    refine ⟨valid.1, valid.2, ePositive, eFits, pPositive, pShort, qPositive, qShort, space,
      ?_, ?_, outFit, sourceFit, wsFit, ?_, outWs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [privateGeometry_stackNat s stackFit]
      simp only [stackBytes] at stackFit ⊢; omega
    · rw [privateGeometry_stackNat s stackFit]
      simp only [stackBytes, VG.Impl.Rsa.X86.PrivChecked.frameBytes] at stackFit ⊢; omega
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [outN, outE, outI, outP, outQ, outDP, outDQ, outQI]
    · rw [privateGeometry_arguments s stackFit argFit]; exact outArgs
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [nWs, eWs, iWs, pWs, qWs, dpWs, dqWs, qiWs]
    · rw [privateGeometry_arguments s stackFit argFit]; exact wsArgs
    · rw [privateGeometry_wholeStack s stackFit]; exact stackOut
    · intro i
      rw [privateGeometry_wholeStack s stackFit]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [stackN, stackE, stackI, stackP, stackQ, stackDP, stackDQ, stackQI]
    · rw [privateGeometry_wholeStack s stackFit]; exact stackWs
    · rw [privateGeometry_wholeStack s stackFit, privateGeometry_arguments s stackFit argFit]; exact stackArgs
  apply PrivEntryInput.ready
  refine ⟨geometry, stackFit, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨sourceFit i, ?_, rfl⟩
    refine ⟨(privateGeometry s).sourceRegion i, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    rw [rd]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
  · rw [wr]
    exact ⟨_, by simp [privateGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [wr]
    exact ⟨_, by simp [privateGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [privateGeometry_arguments s stackFit argFit]
    exact ⟨_, List.mem_append_right _ (by rw [wr]; simp), Region.contains_self _ _⟩
  · intro j hj
    have address : byteAddr (privateGeometry s).stack + BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 4 * j) = argAddr s j := by
      rw [← Offset.add_add]
      change (privateGeometry s).argumentsRegion.base + BitVec.ofNat 64 (4 * j) = _
      rw [privateGeometry_arguments s stackFit argFit]
      simp only [argAddr, Nat.mul_zero, Nat.add_zero]
      have first := byteAddr_add (by omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
      have last := byteAddr_add (by omega : (s.gpr .esp).toNat + (4 + 4 * j) < 2 ^ 32)
      change byteAddr (s.gpr .esp + BitVec.ofNat 32 4) + BitVec.ofNat 64 (4 * j) = byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j))
      rw [first, last, Offset.add_add]
    rw [address]
    change arg s j = _
    have oe : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq outLen
    have ie : arg s 7 = arg s 3 := BitVec.eq_of_toNat_eq inputLen
    have de : arg s 13 = arg s 9 := BitVec.eq_of_toNat_eq dpLen
    have qe : arg s 17 = arg s 9 := BitVec.eq_of_toNat_eq qiLen
    have dqe : arg s 15 = arg s 11 := BitVec.eq_of_toNat_eq dqLen
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
        j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [privateGeometry, PrivGeometry.argument, oe, ie, de, qe, dqe]
    all_goals rfl
  · intro r hr
    have belowRet : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (privateGeometry s).wholeStack := by
      rw [privateGeometry_wholeStack s stackFit]
      have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes)
        (Nat.le_refl stackBytes) (by decide : stackBytes + 4 ≤ 2 ^ 64)
      rw [BitVec.sub_add_cancel] at sep
      exact sep
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact belowRet.sub_right geometry.innerSub
    · exact belowRet.sub_right geometry.calleeSub
    · exact retOut
    · exact retWs
end VG.Proof.Rsa.X86.PrivChecked
