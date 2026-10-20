module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckPrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryPrime
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # Phase-local writes fit the shared parameter-search footprint -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem GenerationGeometry.mutablePart (G : GenerationGeometry) {d n : Nat}
    (start : VG.Impl.Dsa.Generation.Layout.hash ≤ d) (room : d + n ≤ usedBytes G.pLen) :
    (G.part d n).Sub (G.part VG.Impl.Dsa.Generation.Layout.hash
      (usedBytes G.pLen - VG.Impl.Dsa.Generation.Layout.hash)) := by
  have h := G.subarea (d := VG.Impl.Dsa.Generation.Layout.hash) (e := d - VG.Impl.Dsa.Generation.Layout.hash)
    (n := n) (total := usedBytes G.pLen - VG.Impl.Dsa.Generation.Layout.hash) (by omega)
  rw [Nat.add_sub_cancel' start] at h
  exact h

theorem checkPrime_parameterWrites (G : GenerationGeometry) (T : GenerationTape G) (len m : Nat)
    (lo : 4 ≤ len) (hi : len ≤ 384) (words : len % 4 = 0)
    (bits : Spec.RsaKeyGen.bitLength m = 8 * len) (odd : m % 2 = 1) :
    ∀ r ∈ checkPrimeWrites (G.prime T len m lo hi words bits odd) G.frameBase ((G.frame - 16).setWidth 64),
      ∃ outer ∈ parameterWrites G, r.Sub outer := by
  intro r hr
  change r ∈ [⟨(G.frame - 16).setWidth 64, 16⟩, G.part arithmetic arithmeticBytes,
    ⟨(G.pointer witness).setWidth 64, len⟩, ⟨off G.frameBase 64, 16⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨below G.frame 128, by simp [parameterWrites], below_sub (by decide) G.stackSize⟩
  · exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega)⟩
  · rw [G.pointer_addr (by unfold witness usedBytes domainCheck; omega)]
    exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (by unfold witness usedBytes domainCheck; omega)⟩
  · exact ⟨⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩, by simp [parameterWrites],
      Offset.sub_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide)⟩
end VG.Proof.Dsa.X86.Generation
