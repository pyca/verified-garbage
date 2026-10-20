module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateCall
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryStack
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Domain checking shares only its dedicated scratch area and reserved call stack -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem validate_covers {G : GenerationGeometry} {s : State}
    (arena : (⟨G.base, usedBytes G.pLen⟩ : Region) ∈ s.wr) (args : (⟨validateArgsBase G, 24⟩ : Region) ∈ s.wr) :
    Covers (validateRd G ++ validateWr G) (s.rd ++ s.wr) ∧ Covers (validateWr G) s.wr := by
  have pr := validate_packed_room G
  have sr := validate_scratch_room G
  have pointer : InRegions (s.rd ++ s.wr) (off G.base packed) (2 * G.pLen + G.qLen) :=
    ⟨_, List.mem_append_right _ arena, Offset.contains_base _ pr (by have := G.arenaBound; omega)⟩
  have scratch : InRegions s.wr (off G.base domainCheck) (128 * G.pLen) :=
    ⟨_, arena, Offset.contains_base _ sr (by have := G.arenaBound; omega)⟩
  have outgoing : InRegions s.wr (validateArgsBase G) 24 := ⟨_, args, Region.contains_self _ 24⟩
  have writes : Covers (validateWr G) s.wr := Covers.pair (Covers.one scratch) (Covers.one outgoing)
  exact ⟨(Covers.one pointer).cons (by
    intro address len input
    obtain ⟨outer, ho, sub⟩ := writes address len input
    exact ⟨outer, List.mem_append_right _ ho, sub⟩), writes⟩

theorem validate_mutable (G : GenerationGeometry) :
    ∀ r ∈ validateWrites G, ∃ outer ∈ parameterWrites G, r.Sub outer := by
  intro r hr
  simp only [validateWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (validate_scratch_room G)⟩
  · exact ⟨below G.frame 128, by simp [parameterWrites], below_sub (by decide) G.stackSize⟩

theorem validate_frameApart (G : GenerationGeometry) :
    ∀ r ∈ validateWrites G, (⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint r := by
  intro r hr
  simp only [validateWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact G.frame_part (validate_scratch_room G)
  · exact G.frame_below (by decide)

theorem validate_packedApart (G : GenerationGeometry) :
    ∀ r ∈ validateWrites G, (G.part packed (2 * G.pLen + G.qLen)).Disjoint r := by
  intro r hr
  have pw := G.width
  have qw := G.qWidth
  simp only [validateWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact G.parts_disjoint (validate_packed_room G) (validate_scratch_room G)
      (.inl (by unfold packed domainCheck; omega))
  · exact (G.stack_part_native (validate_packed_room G) (by decide : 60 ≤ 128)).symm
end VG.Proof.Dsa.X86.Generation
