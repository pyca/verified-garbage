module

public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Framework.PowLit
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bounds for the three reviewed DSA generation sizes -/

@[expose] public section
namespace VG.Proof.Dsa.Generation

/-- The bits-only generation API has exactly these three pairs. -/
theorem generation_sizes {l n : Nat} (h : VG.Spec.Dsa.subgroupBits l = some n) :
    (l = 1024 ∧ n = 160) ∨ (l = 2048 ∧ n = 256) ∨ (l = 3072 ∧ n = 256) := by
  unfold VG.Spec.Dsa.subgroupBits at h
  split at h
  · simp_all
  · split at h
    · simp_all
    · cases h

/-- Every offset plus contribution index fits in the byte-adder's carry. -/
theorem seed_offset_bound {l n counter j : Nat} (h : VG.Spec.Dsa.subgroupBits l = some n)
    (hc : counter < 4 * l) (hj : j ≤ (l - 1) / n) :
    1 + counter * ((l - 1) / n + 1) + j < 2 ^ 32 := by
  rcases generation_sizes h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals omega

/-- Hash widths divide octets; the final contribution has seven high bits
in its leading byte and fits in the allocated digest. -/
theorem contribution_sizes {l n : Nat} (h : VG.Spec.Dsa.subgroupBits l = some n) :
    n % 8 = 0 ∧ (l - 1) % n % 8 = 7 ∧
      (l - 1) % n < n ∧ 1 ≤ (l - 1) / n + 1 ∧ (l - 1) / n + 1 ≤ 12 := by
  rcases generation_sizes h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

end VG.Proof.Dsa.Generation
