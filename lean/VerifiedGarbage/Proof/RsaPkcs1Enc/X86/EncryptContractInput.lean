module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptABI

/-! # The shared encryption contract establishes the i686 wrapper's inputs -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem encrypt_contract_pre (s : State) (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).pre s) :
    FnInput (encryptGeometry s) (encryptBytes s) s := by
  have H := encryptABI_of h
  have sourceFit : ∀ i, ((encryptGeometry s).sources i).toNat + (encryptGeometry s).sourceLength i ≤ 2 ^ 32 := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    exacts [H.sourceFit0, H.sourceFit1, H.sourceFit2, H.sourceFit3, H.sourceFit4]
  have geometry : (encryptGeometry s).Valid := by
    refine ⟨H.valid.1, H.valid.2, H.ePositive, H.eFits, H.messageFits, H.padding,
      H.preLength, H.space, ?_, ?_, ?_, sourceFit, H.workspaceFit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [encryptGeometry_stackNat s H.stackLow]
      have low := H.stackLow
      simp only [encryptStack] at low
      omega
    · rw [encryptGeometry_stackNat s H.stackLow]
      simp only [encryptStack, VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes] at *
      have := H.stackBound
      omega
    · have fit := H.outputFit
      rw [H.outLen] at fit
      exact fit
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      · have sep := H.outputSource0
        rw [H.outLen] at sep
        exact sep
      · have sep := H.outputSource1
        rw [H.outLen] at sep
        exact sep
      · have sep := H.outputSource2
        rw [H.outLen] at sep
        exact sep
      · have sep := H.outputSource3
        rw [H.outLen] at sep
        exact sep
      · have sep := H.outputSource4
        rw [H.outLen] at sep
        exact sep
    · have sep := H.outputWorkspace
      rw [H.outLen] at sep
      exact sep
    · rw [encryptGeometry_arguments s H.stackLow H.stackBound]
      have sep := H.outputArguments
      rw [H.outLen] at sep
      exact sep
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      exacts [H.sourceWorkspace0, H.sourceWorkspace1, H.sourceWorkspace2, H.sourceWorkspace3, H.sourceWorkspace4]
    · rw [encryptGeometry_arguments s H.stackLow H.stackBound]
      exact H.workspaceArguments
    · rw [encryptGeometry_wholeStack s H.stackLow]
      have sep := H.stackOutput
      rw [H.outLen] at sep
      exact sep
    · intro i
      rw [encryptGeometry_wholeStack s H.stackLow]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      exacts [H.stackSource0, H.stackSource1, H.stackSource2, H.stackSource3, H.stackSource4]
    · rw [encryptGeometry_wholeStack s H.stackLow]
      exact H.stackWorkspace
    · rw [encryptGeometry_wholeStack s H.stackLow, encryptGeometry_arguments s H.stackLow H.stackBound]
      exact H.stackArguments
  apply EntryInput.ready
  refine ⟨geometry, H.stackLow, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨sourceFit i, ?_, rfl⟩
    refine ⟨(encryptGeometry s).sourceRegion i, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    rw [H.rd]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  · rw [H.wr]
    have out : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq H.outLen
    exact ⟨_, by simp [encryptGeometry, byteAddr, argumentPointer, out], Region.contains_self _ _⟩
  · rw [H.wr]
    exact ⟨_, by simp [encryptGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [encryptGeometry_arguments s H.stackLow H.stackBound]
    exact ⟨_, List.mem_append_right _ (by rw [H.wr]; simp), Region.contains_self _ _⟩
  · intro j hj
    have address : byteAddr (encryptGeometry s).stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20 + 4 * j) = argAddr s j := by
      rw [← Offset.add_add]
      change (encryptGeometry s).argumentsRegion.base + BitVec.ofNat 64 (4 * j) = _
      rw [encryptGeometry_arguments s H.stackLow H.stackBound]
      simp only [argAddr, Nat.mul_zero, Nat.add_zero]
      have first := byteAddr_add (by have := H.stackBound; omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
      have last := byteAddr_add (by have := H.stackBound; omega : (s.gpr .esp).toNat + (4 + 4 * j) < 2 ^ 32)
      change byteAddr (s.gpr .esp + BitVec.ofNat 32 4) + BitVec.ofNat 64 (4 * j) = byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j))
      rw [first, last, Offset.add_add]
    rw [address]
    change arg s j = _
    have oe : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq H.outLen
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [encryptGeometry, Geometry.argument, oe]
    all_goals rfl
  · intro r hr
    have belowRet : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (encryptGeometry s).wholeStack := by
      rw [encryptGeometry_wholeStack s H.stackLow]
      have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack)
        (Nat.le_refl encryptStack) (by decide : encryptStack + 4 ≤ 2 ^ 64)
      rw [BitVec.sub_add_cancel] at sep
      exact sep
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact belowRet.sub_right geometry.innerSub
    · exact belowRet.sub_right geometry.calleeSub
    · have sep := H.returnOutput
      rw [H.outLen] at sep
      exact sep
    · exact H.returnWorkspace

end VG.Proof.RsaPkcs1Enc.X86.Enc
