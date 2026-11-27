module

public import VerifiedGarbage.Proof.MlDsa.Round.Decompose
public import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-DSA on AArch64: the two values of `γ₂`

`γ₂` is one of its two values (`IsG`, `isG_of_mem`, `mem_of_isG`), for which
the code's modulus `dMod` is that of `Proof/MlDsa/Round/Decompose.lean`
(`dMod_eq`, `hbM_pos`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (q)
open VG.Proof.MlDsa (gamma2s)

/-- `γ₂` is one of its two values. -/
abbrev IsG (g : Nat) : Prop := g = g32 ∨ g = g88

theorem isG_of_mem {g : Nat} (h : g ∈ gamma2s) : IsG g := by
  rcases mem_gamma2s h with e | e
  · exact .inr e
  · exact .inl e

theorem mem_of_isG {g : Nat} (h : IsG g) : g ∈ gamma2s := by
  rcases h with rfl | rfl <;> decide

theorem dMod_eq {g : Nat} (h : IsG g) : dMod g = hbM g := by rcases h with rfl | rfl <;> rfl

theorem hbM_pos {g : Nat} (h : IsG g) : 0 < hbM g := by rcases h with rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Round
