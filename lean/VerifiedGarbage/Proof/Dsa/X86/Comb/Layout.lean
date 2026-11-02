module

public import VerifiedGarbage.Impl.Dsa.X86.Comb
public import VerifiedGarbage.Proof.Dsa.FixedBaseCombContract

/-! Bounds for the five supported DSA comb layouts, including the padded
2048/160 domain. The retained context never overlaps arithmetic scratch. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG.Impl.Dsa.X86.Comb

/-- Supported modulus-word and exponent-word counts. -/
def Supported (n e : Nat) : Prop :=
  (n = 16 ∧ e = 5) ∨ (n = 32 ∧ e = 5) ∨ (n = 32 ∧ e = 7) ∨
    (n = 32 ∧ e = 8) ∨ (n = 48 ∧ e = 8)

theorem layout_valid {n e : Nat} (h : Supported n e) :
    VG.Proof.Dsa.FixedBaseComb.LayoutValid (layout n e) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> unfold VG.Proof.Dsa.FixedBaseComb.LayoutValid <;> decide

/-- The table and prefix fit in the existing key-generation allocation. -/
theorem workspace_fits {n e : Nat} (h : Supported n e) :
    (layout n e).size ≤ 8 * (64 * (8*n) + 1024) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Every exponent includes enough padding for the fixed five-tooth schedule. -/
theorem exponent_fits {n e : Nat} (h : Supported n e) :
    4 * ((5 * VG.Spec.Rsa.FixedBaseComb.rows (32*e) + 31) / 32) ≤
      VG.Impl.Mont.X86.Dynamic.stride n := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

end VG.Proof.Dsa.X86.Comb
