module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Framework.Omega

/-! # The native parameter generator fits the existing public scratch contract -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Impl.Dsa.Generation.Layout

theorem generation_layout_fits {pLen qLen : Nat} (h : Spec.Dsa.generationLengthsValid pLen qLen) :
    usedBytes pLen ≤ 8 * Spec.Dsa.generationScratchWords pLen := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Every reserved area is inside the public scratch allocation. -/
theorem generation_area_bound {pLen qLen : Nat} (h : Spec.Dsa.generationLengthsValid pLen qLen)
    {r : Nat × Nat} (hr : r ∈ areas pLen) : r.1 + r.2 ≤ usedBytes pLen := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [areas, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- At each supported size, all reserved areas are pairwise disjoint. -/
theorem generation_areas_disjoint {pLen qLen : Nat} (h : Spec.Dsa.generationLengthsValid pLen qLen) :
    (areas pLen).Pairwise (fun a b => a.1 + a.2 ≤ b.1) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

end VG.Proof.Dsa.Generation
