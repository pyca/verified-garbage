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

end VG.Proof.Dsa.Generation
