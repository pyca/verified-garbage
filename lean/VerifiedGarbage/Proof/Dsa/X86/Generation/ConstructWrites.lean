module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributions
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PConstruct
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Candidate construction preserves frame words and the accepted q -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

def constructionWrites {H : Hash} (K : HashOK H) (G : GenerationGeometry) (T : GenerationTape G) (offset : Nat) : List Region :=
  (G.contributions T offset).allWrites K ++ [G.part shaped G.pLen, G.part arithmetic arithmeticBytes,
    G.part p G.pLen, G.part exponent G.pLen]

theorem contribution_mutable {H : Hash} (K : HashOK H) (G : GenerationGeometry) (T : GenerationTape G)
    (offset : Nat) (len : T.bytes.length = G.qLen) (final : H.F = G.qLen)
    {r : Region} (hr : r ∈ (G.contributions T offset).allWrites K) :
    ∃ outer ∈ parameterWrites G, r.Sub outer := by
  obtain ⟨j, hj, hr⟩ := List.mem_flatMap.mp hr
  have jb : j ≤ G.contributionCount := by have := List.mem_range.mp hj; change j < G.contributionCount + 1 at this; omega
  rw [G.contribution_writes K T offset len final jb] at hr
  have qw := G.qWidth
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (by unfold wrappedSeed usedBytes domainCheck; omega)⟩
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by unfold VG.Impl.Dsa.Generation.Layout.hash; omega) (by
      have := K.hSB; unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this])⟩
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by unfold VG.Impl.Dsa.Generation.Layout.hash hashes; omega) (G.contribution_room jb)⟩
  · exact ⟨_, List.mem_cons_self, G.mutablePart (Nat.le_refl _) (by
      have := K.hWb; have hw := K.hW; unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this, hw])⟩
  · exact ⟨below G.frame 128, by simp [parameterWrites], below_sub (by decide) G.stackSize⟩

theorem construction_mutable {H : Hash} (K : HashOK H) (G : GenerationGeometry) (T : GenerationTape G)
    (offset : Nat) (len : T.bytes.length = G.qLen) (final : H.F = G.qLen) :
    ∀ r ∈ constructionWrites K G T offset, ∃ outer ∈ parameterWrites G, r.Sub outer := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact contribution_mutable K G T offset len final hr
  have pw := G.width
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals refine ⟨_, List.mem_cons_self, G.mutablePart (by decide) ?_⟩
  all_goals dsimp only [shaped, arithmetic, arithmeticBytes, p, exponent, usedBytes, domainCheck] <;> omega

theorem construction_frameApart {H : Hash} {K : HashOK H} {G : GenerationGeometry}
    {T : GenerationTape G} {offset qvalue : Nat} {s : State}
    (R : PConstructInputs K G (G.contributions T offset) qvalue s) :
    ∀ r ∈ constructionWrites K G T offset,
      (⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨j, hj, hr⟩ := List.mem_flatMap.mp hr
    exact R.layout.frameApart j (by have := List.mem_range.mp hj; omega) r hr
  have pw := G.width
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals apply G.frame_part
  all_goals dsimp only [shaped, arithmetic, arithmeticBytes, p, exponent, usedBytes, domainCheck] <;> omega

theorem construction_qApart {H : Hash} {K : HashOK H} {G : GenerationGeometry}
    {T : GenerationTape G} {offset qvalue : Nat} {s : State}
    (R : PConstructInputs K G (G.contributions T offset) qvalue s) :
    ∀ r ∈ constructionWrites K G T offset, (G.part q G.qLen).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact R.qApart r hr
  have pw := G.width
  have qw := G.qWidth
  have qr : q + G.qLen ≤ usedBytes G.pLen := by unfold q usedBytes domainCheck; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact G.parts_disjoint qr (by unfold shaped usedBytes domainCheck; omega) (.inr (by unfold shaped q; omega))
  all_goals apply G.parts_disjoint qr
  all_goals dsimp only [q, arithmetic, arithmeticBytes, p, exponent, usedBytes, domainCheck] <;> omega
end VG.Proof.Dsa.X86.Generation
