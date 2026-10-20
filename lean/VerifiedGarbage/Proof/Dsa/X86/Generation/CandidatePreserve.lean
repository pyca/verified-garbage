module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ConstructWrites
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateTestState
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Candidate phases leave persistent inputs and the retry controller intact -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem candidateTest_bufferApart (G : GenerationGeometry) {d n : Nat}
    (room : d + n ≤ usedBytes G.pLen) (before : d + n ≤ witness) :
    ∀ r ∈ candidateTestWrites G, (G.part d n).Disjoint r := by
  intro r hr
  have ar : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  have wr : witness + 384 ≤ usedBytes G.pLen := by unfold witness usedBytes domainCheck; omega
  simp only [candidateTestWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact G.parts_disjoint room ar (.inl (by unfold witness arithmetic at *; omega))
  · exact G.parts_disjoint room wr (.inl before)
  · exact (G.frame_part room).symm
  · exact (G.stack_part_native room (by decide : 16 ≤ 128)).symm

theorem candidateTest_controlApart (G : GenerationGeometry) :
    ∀ r ∈ candidateTestWrites G, (G.part VG.Impl.Dsa.Generation.Layout.control 8).Disjoint r := by
  intro r hr
  have cr : VG.Impl.Dsa.Generation.Layout.control + 8 ≤ usedBytes G.pLen := by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega
  have ar : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  have wr : witness + 384 ≤ usedBytes G.pLen := by unfold witness usedBytes domainCheck; omega
  simp only [candidateTestWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact G.parts_disjoint cr ar (.inl (by decide))
  · exact G.parts_disjoint cr wr (.inr (by decide))
  · exact (G.frame_part cr).symm
  · exact (G.stack_part_native cr (by decide : 16 ≤ 128)).symm

theorem contribution_bufferApart {H : Hash} (K : HashOK H) (G : GenerationGeometry) (T : GenerationTape G)
    (offset : Nat) (len : T.bytes.length = G.qLen) (final : H.F = G.qLen)
    {d n : Nat} (afterHashes : hashes + 384 ≤ d) (room : d + n ≤ usedBytes G.pLen) :
    ∀ r ∈ (G.contributions T offset).allWrites K, (G.part d n).Disjoint r := by
  intro r hr
  obtain ⟨j, hj, hr⟩ := List.mem_flatMap.mp hr
  have jb : j ≤ G.contributionCount := by have := List.mem_range.mp hj; change j < G.contributionCount + 1 at this; omega
  rw [G.contribution_writes K T offset len final jb] at hr
  have qw := G.qWidth
  have stateBound := K.hSB
  have workBound := K.hWb
  have work := K.hW
  have contrib := G.contribution_part jb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact G.parts_disjoint room (by unfold wrappedSeed usedBytes domainCheck; omega) (.inr (by unfold wrappedSeed hashes at *; omega))
  · exact G.parts_disjoint room (by
      unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [stateBound]) (.inr (by
      unfold VG.Impl.Dsa.Generation.Layout.hash hashes at *; omega_using [stateBound, afterHashes]))
  · exact G.parts_disjoint room (G.contribution_room jb) (.inr (by omega))
  · exact G.parts_disjoint room (by
      unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [workBound, work]) (.inr (by
      unfold VG.Impl.Dsa.Generation.Layout.hash hashes at *; omega_using [workBound, work, afterHashes]))
  · exact (G.stack_part_native room (by decide : 48 ≤ 128)).symm

theorem construction_controlApart {H : Hash} (K : HashOK H) (G : GenerationGeometry) (T : GenerationTape G)
    (offset : Nat) (len : T.bytes.length = G.qLen) (final : H.F = G.qLen) :
    ∀ r ∈ constructionWrites K G T offset, (G.part VG.Impl.Dsa.Generation.Layout.control 8).Disjoint r := by
  intro r hr
  have cr : VG.Impl.Dsa.Generation.Layout.control + 8 ≤ usedBytes G.pLen := by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega
  rcases List.mem_append.mp hr with hr | hr
  · exact contribution_bufferApart K G T offset len final (by decide) cr r hr
  have pw := G.width
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals apply G.parts_disjoint cr
  all_goals dsimp only [VG.Impl.Dsa.Generation.Layout.control, shaped, arithmetic, arithmeticBytes, p, exponent, usedBytes, domainCheck] <;> omega
theorem candidateTest_mutable (G : GenerationGeometry) :
    ∀ r ∈ candidateTestWrites G, ∃ outer ∈ parameterWrites G, r.Sub outer := by
  intro r hr
  simp only [candidateTestWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega)⟩
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (by unfold witness usedBytes domainCheck; omega)⟩
  · exact ⟨_, by simp [parameterWrites], fun _ h => h⟩
  · exact ⟨below G.frame 128, by simp [parameterWrites], below_sub (by decide) G.stackSize⟩

theorem CandidateTestResult.keep {P : SearchContextPlan} {value used : Nat} {result : PrimeStepResult}
    {s t : State} {rs : List Region} {regs : List Reg} (R : CandidateTestResult P value used result s)
    (O : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, (P.geometry.part arithmetic arithmeticBytes).Disjoint r)
    (K : Keeps regs s t) (sp : .esp ∉ regs) : CandidateTestResult P value used result t := by
  refine ⟨R.monotone, R.bound, R.status, R.spec, ?_⟩
  intro accepted
  obtain ⟨D, ready⟩ := R.accepted accepted
  exact ⟨D, ready.frame O apart K sp⟩
end VG.Proof.Dsa.X86.Generation
