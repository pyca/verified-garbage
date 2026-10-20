module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyConstants
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract

/-! The selected controller contract adds exactly its policy's public tables. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm

theorem selected_pre {sampling : GenerationPolicy} {s : State} :
    (sampling.searchContract (KeyConstants.abi sampling) (stackUse sampling)).pre s ↔
      (sampling.searchContract abi (stackUse sampling)).pre (stripConsts (KeyConstants.consts sampling) s) ∧
        ConstsOk (KeyConstants.consts sampling) (stackUse sampling) s := by
  cases sampling with
  | full | cached =>
    simp only [KeyConstants.consts, KeyConstants.abi_full, KeyConstants.abi_cached]
    have strip : stripConsts [] s = s := by simp [stripConsts, State.withRegions]
    rw [strip]
    simp [ConstsOk, Abi.constRegions, Abi.constsHeld]
  | vetted =>
    unfold GenerationPolicy.searchContract GenerationPolicy.legacySearchContract KeyConstants.abi KeyConstants.consts
    exact pre_consts

theorem selected_post {sampling : GenerationPolicy} {s t : State} :
    (sampling.searchContract (KeyConstants.abi sampling) (stackUse sampling)).post s t ↔
      (sampling.searchContract abi (stackUse sampling)).post s t := by
  cases sampling with
  | full | cached => rfl
  | vetted =>
    unfold GenerationPolicy.searchContract GenerationPolicy.legacySearchContract KeyConstants.abi KeyConstants.consts
    exact post_consts

theorem selected_pub {sampling : GenerationPolicy} {s t : State} :
    (sampling.searchContract (KeyConstants.abi sampling) (stackUse sampling)).pub s t ↔
      (sampling.searchContract abi (stackUse sampling)).pub s t ∧
        KeyConstants.tablePtr sampling s = KeyConstants.tablePtr sampling t := by
  cases sampling with
  | full | cached => simp only [KeyConstants.abi_full, KeyConstants.abi_cached, KeyConstants.tablePtr, and_true]
  | vetted =>
    have bridge : (GenerationPolicy.vetted.searchContract (KeyConstants.abi .vetted) (stackUse .vetted)).pub s t ↔
        (GenerationPolicy.vetted.searchContract abi (stackUse .vetted)).pub s t ∧
          ∀ c ∈ VG.Impl.Ffdh.Arm.VettedGroups.tableConsts, symAddr s c.1 = symAddr t c.1 := by
      unfold GenerationPolicy.searchContract GenerationPolicy.legacySearchContract KeyConstants.abi KeyConstants.consts
      exact pub_consts
    constructor
    · intro h
      have parts := bridge.mp h
      exact ⟨parts.1, symAddr_eq_iff.mp (parts.2 _ List.mem_cons_self)⟩
    · rintro ⟨h, table⟩
      apply bridge.mpr
      refine ⟨h, ?_⟩
      intro c member
      simp only [VG.Impl.Ffdh.Arm.VettedGroups.tableConsts, List.mem_cons, List.not_mem_nil, or_false] at member
      subst c
      exact symAddr_eq_iff.mpr table

theorem selected_attempt_pre {sampling : GenerationPolicy} {s : State} :
    (sampling.attemptContract (KeyConstants.abi sampling) 176).pre s ↔
      (sampling.attemptContract abi 176).pre (stripConsts (KeyConstants.consts sampling) s) ∧
        ConstsOk (KeyConstants.consts sampling) 176 s := by
  cases sampling with
  | full | cached =>
    simp only [KeyConstants.consts, KeyConstants.abi_full, KeyConstants.abi_cached]
    have strip : stripConsts [] s = s := by simp [stripConsts, State.withRegions]
    rw [strip]
    simp [ConstsOk, Abi.constRegions, Abi.constsHeld]
  | vetted =>
    unfold GenerationPolicy.attemptContract GenerationPolicy.legacyAttemptContract KeyConstants.abi KeyConstants.consts
    exact pre_consts

theorem selected_attempt_post {sampling : GenerationPolicy} {s t : State} :
    (sampling.attemptContract (KeyConstants.abi sampling) 176).post s t ↔
      (sampling.attemptContract abi 176).post s t := by
  cases sampling with
  | full | cached => rfl
  | vetted =>
    unfold GenerationPolicy.attemptContract GenerationPolicy.legacyAttemptContract KeyConstants.abi KeyConstants.consts
    exact post_consts

theorem selected_attempt_pub {sampling : GenerationPolicy} {s t : State} :
    (sampling.attemptContract (KeyConstants.abi sampling) 176).pub s t ↔
      (sampling.attemptContract abi 176).pub s t ∧
        KeyConstants.tablePtr sampling s = KeyConstants.tablePtr sampling t := by
  cases sampling with
  | full | cached => simp only [KeyConstants.abi_full, KeyConstants.abi_cached, KeyConstants.tablePtr, and_true]
  | vetted =>
    have bridge : (GenerationPolicy.vetted.attemptContract (KeyConstants.abi .vetted) 176).pub s t ↔
        (GenerationPolicy.vetted.attemptContract abi 176).pub s t ∧
          ∀ c ∈ VG.Impl.Ffdh.Arm.VettedGroups.tableConsts, symAddr s c.1 = symAddr t c.1 := by
      unfold GenerationPolicy.attemptContract GenerationPolicy.legacyAttemptContract KeyConstants.abi KeyConstants.consts
      exact pub_consts
    constructor
    · intro h
      have parts := bridge.mp h
      exact ⟨parts.1, symAddr_eq_iff.mp (parts.2 _ List.mem_cons_self)⟩
    · rintro ⟨h, table⟩
      apply bridge.mpr
      refine ⟨h, ?_⟩
      intro c member
      simp only [VG.Impl.Ffdh.Arm.VettedGroups.tableConsts, List.mem_cons, List.not_mem_nil, or_false] at member
      subst c
      exact symAddr_eq_iff.mpr table

end VG.Proof.Ffdh.Arm.KeySearch
