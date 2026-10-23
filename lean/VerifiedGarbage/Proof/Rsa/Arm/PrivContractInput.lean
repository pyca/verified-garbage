module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivContractGeometry
public import VerifiedGarbage.Proof.Rsa.Arm.PrivFnInput
import VerifiedGarbage.Proof.Rsa.Arm.PrivEntryReady
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Shared private RSA preconditions establish the native wrapper inputs -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem private_contract_pre (s : State) (h : (Spec.Rsa.privateCheckedContract abi stackBytes).pre s) :
    PrivFnInput (privateGeometry s) (privateBytes s) s := by
  sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have addr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [addr] at h
  obtain ⟨stackFit, argFit, rd, wr, outN, outE, outI, outP, outQ, outDP, outDQ, outQI, outWs, outArgs,
    nWs, eWs, iWs, pWs, qWs, dpWs, dqWs, qiWs, wsArgs,
    stackOut, stackN, stackE, stackI, stackP, stackQ, stackDP, stackDQ, stackQI, stackWs, stackArgs,
    outFit, nFit, eFit, iFit, pFit, qFit, dpFit, dqFit, qiFit, wsFit,
    valid, outLen, inputLen, ePositive, eFits, pPositive, pShort, qPositive, qShort, dpLen, qiLen, dqLen, space⟩ := h
  rw [outLen] at wr outN outE outI outP outQ outDP outDQ outQI outWs outArgs stackOut outFit
  rw [inputLen] at rd outI iWs stackI iFit
  rw [dpLen] at rd outDP dpWs stackDP dpFit
  rw [dqLen] at rd outDQ dqWs stackDQ dqFit
  rw [qiLen] at rd outQI qiWs stackQI qiFit
  rw [show (stackArg s 15).toNat * 8 = 8 * (stackArg s 15).toNat from Nat.mul_comm _ _]
    at wr outWs nWs eWs iWs pWs qWs dpWs dqWs qiWs wsArgs stackWs wsFit
  have sourceFit : ∀ i, ((privateGeometry s).sources i).toNat + (privateGeometry s).sourceLength i ≤ 2 ^ 32 := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [nFit, eFit, iFit, pFit, qFit, dpFit, dqFit, qiFit]
  have geometry : (privateGeometry s).Valid := by
    refine ⟨valid.1, valid.2, ePositive, eFits, pPositive, pShort, qPositive, qShort, space,
      ?_, ?_, outFit, sourceFit, wsFit, ?_, outWs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [privateGeometry_stackNat s stackFit]
      simp only [stackBytes, frameBytes] at stackFit ⊢; omega_arith
    · rw [privateGeometry_stackNat s stackFit]
      simp only [stackBytes, frameBytes] at stackFit ⊢; omega_arith
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [outN, outE, outI, outP, outQ, outDP, outDQ, outQI]
    · rw [privateGeometry_arguments s stackFit]; exact outArgs
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [nWs, eWs, iWs, pWs, qWs, dpWs, dqWs, qiWs]
    · rw [privateGeometry_arguments s stackFit]; exact wsArgs
    · rw [privateGeometry_wholeStack s stackFit]; exact stackOut
    · intro i
      rw [privateGeometry_wholeStack s stackFit]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [stackN, stackE, stackI, stackP, stackQ, stackDP, stackDQ, stackQI]
    · rw [privateGeometry_wholeStack s stackFit]; exact stackWs
    · rw [privateGeometry_wholeStack s stackFit, privateGeometry_arguments s stackFit]; exact stackArgs
  apply PrivEntryInput.ready
  refine ⟨geometry, stackFit, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, by simp [privateGeometry]⟩
  · intro i
    refine ⟨sourceFit i, ?_, rfl⟩
    refine ⟨(privateGeometry s).sourceRegion i, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    rw [rd]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith) with
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
    exact ⟨_, by simp [privateGeometry, State.addr], Region.contains_self _ _⟩
  · rw [wr]
    exact ⟨_, by simp [privateGeometry, State.addr], Region.contains_self _ _⟩
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp), Region.contains_self _ _⟩
  · intro j hj
    have read : s.mem.readW (off (State.addr s.sp) (4 * j)) 32 = stackArg s j := by
      unfold stackArg stackArgAddr
      rw [addr_add (by omega_arith : s.sp.toNat + 4 * j < 2 ^ 32)]
    rw [read]
    have ie : stackArg s 3 = s.gpr .r3 := BitVec.eq_of_toNat_eq inputLen
    have de : stackArg s 9 = stackArg s 5 := BitVec.eq_of_toNat_eq dpLen
    have qe : stackArg s 13 = stackArg s 5 := BitVec.eq_of_toNat_eq qiLen
    have dqe : stackArg s 11 = stackArg s 7 := BitVec.eq_of_toNat_eq dqLen
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 by omega_arith) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [privateGeometry, PrivGeometry.argument, ie, de, qe, dqe]
    all_goals rfl
end VG.Proof.Rsa.Arm
