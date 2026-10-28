module

public import VerifiedGarbage.Proof.Framework.Mem

/-! # Disjoint regions of the address space, as bounds on their addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG

theorem disjoint_bounds {a b : Addr} {n k : Nat}
    (positive : 0 < n) (otherPositive : 0 < k) (D : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) :
    a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat := by
  refine Classical.byContradiction fun bad => ?_
  by_cases order : a.toNat ≤ b.toNat
  · apply D b
    · change (b - a).toNat + 1 ≤ n
      rw [BitVec.toNat_sub]
      have := a.isLt
      have := b.isLt
      omega
    · change (b - b).toNat + 1 ≤ k
      rw [BitVec.sub_self]
      change 0 + 1 ≤ k
      omega
  · apply D a
    · change (a - a).toNat + 1 ≤ n
      rw [BitVec.sub_self]
      change 0 + 1 ≤ n
      omega
    · change (a - b).toNat + 1 ≤ k
      rw [BitVec.toNat_sub]
      have := a.isLt
      have := b.isLt
      omega

end VG.Proof.RsaKeyGen.X86.Key
