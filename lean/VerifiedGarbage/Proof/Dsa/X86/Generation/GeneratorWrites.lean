module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchGeneratorMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Generator search writes only its arithmetic area, witness buffer, frame, and g -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def generationGeneratorWrites (G : GenerationGeometry) : List Region :=
  [G.part arithmetic arithmeticBytes, G.part witness G.pLen,
   ⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩, G.part g G.pLen]

theorem searchGeneratorWrites {P : PSearchPlan} {value : Nat} {W : Nat → BitVec 32} {s : State}
    (R : PSearchMemory P W s) (A : PSearchAccepted P value s) :
    (searchGeneratorPlan R A).changed = generationGeneratorWrites P.context.geometry := by
  change [P.context.geometry.part arithmetic arithmeticBytes,
    ⟨(P.context.geometry.pointer witness).setWidth 64, P.context.geometry.pLen⟩,
    ⟨P.context.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩,
    ⟨(P.context.geometry.pointer g).setWidth 64, P.context.geometry.pLen⟩] = _
  rw [P.context.geometry.pointer_addr (by unfold witness usedBytes domainCheck; omega),
    P.context.geometry.pointer_addr (by unfold g usedBytes domainCheck; omega)]
  rfl

theorem generatorWrites_mutable (G : GenerationGeometry) :
    ∀ r ∈ generationGeneratorWrites G, ∃ outer ∈ parameterWrites G, r.Sub outer := by
  intro r hr
  have pw := G.width
  simp only [generationGeneratorWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega)⟩
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (by unfold witness usedBytes domainCheck; omega)⟩
  · exact ⟨_, by simp [parameterWrites], fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (by unfold g usedBytes domainCheck; omega)⟩

theorem generatorWrites_bufferApart (G : GenerationGeometry) {d n : Nat}
    (room : d + n ≤ usedBytes G.pLen) (before : d + n ≤ g) :
    ∀ r ∈ generationGeneratorWrites G, (G.part d n).Disjoint r := by
  intro r hr
  have pw := G.width
  simp only [generationGeneratorWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact G.parts_disjoint room (by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega)
      (.inl (by unfold g arithmetic at *; omega))
  · exact G.parts_disjoint room (by unfold witness usedBytes domainCheck; omega)
      (.inl (by unfold g witness at *; omega))
  · exact (G.frame_part room).symm
  · exact G.parts_disjoint room (by unfold g usedBytes domainCheck; omega) (.inl before)
end VG.Proof.Dsa.X86.Generation
