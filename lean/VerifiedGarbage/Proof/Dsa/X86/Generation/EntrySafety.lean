module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Safety
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall

/-! # Stack-pointer safety of the generated entry and every supported width -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem generate_safe {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    (plen qlen : Nat) (width : plen = 128 ∧ qlen = 20 ∨ plen = 256 ∧ qlen = 32 ∨ plen = 384 ∧ qlen = 32) :
    generationSafe (generate H F.name F.code plen qlen) := by
  have hash := seedHash_safe K qlen
  have hashes := pHashPrefix_safe K qlen ((8 * plen - 1) / (8 * qlen)) (((8 * plen - 1) / (8 * qlen)) + 1)
  have table := trialTable_safe 1024
  have check := noSp_safe F.noSp
  unfold generationSafe at *
  simp only [generate, initializeSearch, parameterSearch, tapeLoop, tapeIteration, parameterBody,
    qPhase, qBuild, qCandidate, onSuccess, nativePSearch, pSearch, pSearchIteration, pAttempt, pConstruct,
    pHashesShape, pHashes, finishDomain, validate, Code.all, hash, hashes, table, check]
  rcases width with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [Bool.and_eq_true]
    repeat apply And.intro
    all_goals first | rfl | decide +kernel

theorem entry_safe (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn) :
    generationSafe (code H.sha1 H.sha256 F.name F.code) := by
  have one := generate_safe H.h1 F 128 20 (.inl ⟨rfl, rfl⟩)
  have two := generate_safe H.h256 F 256 32 (.inr (.inl ⟨rfl, rfl⟩))
  have three := generate_safe H.h256 F 384 32 (.inr (.inr ⟨rfl, rfl⟩))
  unfold generationSafe at *
  simp only [code, entryBody, dispatch, Code.all, one, two, three]
  rfl
end VG.Proof.Dsa.X86.Generation
