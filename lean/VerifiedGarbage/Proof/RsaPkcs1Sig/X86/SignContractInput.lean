module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignABI

/-! # Shared private RSA preconditions establish the i686 wrapper inputs -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem sign_contract_pre (s : State) (h : (Spec.RsaPkcs1Sig.signContract abi sigStack).pre s) :
    FnInput (signGeometry s) (signBytes s) s := by
  obtain ⟨stackFit, argFit, rd, wr, outN, outE, outI, outP, outQ, outDP, outDQ, outQI, outWs, outArgs,
    nWs, eWs, iWs, pWs, qWs, dpWs, dqWs, qiWs, wsArgs,
    stackOut, stackN, stackE, stackI, stackP, stackQ, stackDP, stackDQ, stackQI, stackWs, stackArgs,
    retOut, retWs, outFit, nFit, eFit, iFit, pFit, qFit, dpFit, dqFit, qiFit, wsFit,
    valid, outLen, ePositive, eFits, pPositive, pShort, qPositive, qShort, dpLen, qiLen, dqLen, space⟩ := signABI_of h
  rw [outLen] at wr outN outE outI outP outQ outDP outDQ outQI outWs outArgs stackOut outFit retOut
  rw [dpLen] at rd outDP dpWs stackDP dpFit
  rw [dqLen] at rd outDQ dqWs stackDQ dqFit
  rw [qiLen] at rd outQI qiWs stackQI qiFit
  rw [show (arg s 20).toNat * 8 = 8 * (arg s 20).toNat from Nat.mul_comm _ _]
    at wr outWs nWs eWs iWs pWs qWs dpWs dqWs qiWs wsArgs stackWs wsFit retWs
  have sourceFit : ∀ i, ((signGeometry s).sources i).toNat + (signGeometry s).sourceLength i ≤ 2 ^ 32 := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [nFit, eFit, iFit, pFit, qFit, dpFit, dqFit, qiFit]
  have geometry : (signGeometry s).Valid := by
    refine ⟨valid.1, valid.2, (arg s 8).isLt, ePositive, eFits, pPositive, pShort, qPositive, qShort, space,
      ?_, ?_, outFit, sourceFit, wsFit, ?_, outWs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [signGeometry_stackNat s stackFit]
      simp only [sigStack, calleeBytes] at stackFit ⊢; omega
    · rw [signGeometry_stackNat s stackFit]
      simp only [sigStack, VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes] at stackFit ⊢; omega
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [outN, outE, outI, outP, outQ, outDP, outDQ, outQI]
    · rw [signGeometry_arguments s stackFit argFit]; exact outArgs
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [nWs, eWs, iWs, pWs, qWs, dpWs, dqWs, qiWs]
    · rw [signGeometry_arguments s stackFit argFit]; exact wsArgs
    · rw [signGeometry_wholeStack s stackFit]; exact stackOut
    · intro i
      rw [signGeometry_wholeStack s stackFit]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [stackN, stackE, stackI, stackP, stackQ, stackDP, stackDQ, stackQI]
    · rw [signGeometry_wholeStack s stackFit]; exact stackWs
    · rw [signGeometry_wholeStack s stackFit, signGeometry_arguments s stackFit argFit]; exact stackArgs
  apply EntryInput.ready
  refine ⟨geometry, stackFit, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨sourceFit i, ?_, rfl⟩
    refine ⟨(signGeometry s).sourceRegion i, List.mem_append_left _ ?_, Region.contains_self _ _⟩
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
    exact ⟨_, by simp [signGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [wr]
    exact ⟨_, by simp [signGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [signGeometry_arguments s stackFit argFit]
    exact ⟨_, List.mem_append_right _ (by rw [wr]; simp), Region.contains_self _ _⟩
  · intro j hj
    have address : byteAddr (signGeometry s).stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * j) = argAddr s j := by
      rw [← Offset.add_add]
      change (signGeometry s).argumentsRegion.base + BitVec.ofNat 64 (4 * j) = _
      rw [signGeometry_arguments s stackFit argFit]
      simp only [argAddr, Nat.mul_zero, Nat.add_zero]
      have first := byteAddr_add (by omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
      have last := byteAddr_add (by omega : (s.gpr .esp).toNat + (4 + 4 * j) < 2 ^ 32)
      change byteAddr (s.gpr .esp + BitVec.ofNat 32 4) + BitVec.ofNat 64 (4 * j) = byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j))
      rw [first, last, Offset.add_add]
    rw [address]
    change arg s j = _
    have oe : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq outLen
    have de : arg s 14 = arg s 10 := BitVec.eq_of_toNat_eq dpLen
    have qe : arg s 18 = arg s 10 := BitVec.eq_of_toNat_eq qiLen
    have dqe : arg s 16 = arg s 12 := BitVec.eq_of_toNat_eq dqLen
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
        j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [signGeometry, Geometry.argument, oe, de, qe, dqe]
    all_goals rfl
  · intro r hr
    have belowRet : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (signGeometry s).wholeStack := by
      rw [signGeometry_wholeStack s stackFit]
      have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack)
        (Nat.le_refl sigStack) (by decide : sigStack + 4 ≤ 2 ^ 64)
      rw [BitVec.sub_add_cancel] at sep
      exact sep
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact belowRet.sub_right geometry.innerSub
    · exact belowRet.sub_right geometry.calleeSub
    · exact retOut
    · exact retWs
end VG.Proof.RsaPkcs1Sig.X86.Sgn
