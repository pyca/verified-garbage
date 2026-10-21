module

public import Init.Data.Nat.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-! # Five public bits multiply a prepared array stride by its index -/

@[expose] public section
namespace VG.Proof.MillerRabin

def indexStep (j c bit : Nat) : Nat := 2 * c + if j / 2 ^ bit % 2 = 1 then 1 else 0

def indexFold (j : Nat) (bits : List Nat) (c : Nat) : Nat := bits.foldl (indexStep j) c

theorem index5_eq {j : Nat} (bound : j < 32) : indexFold j [4, 3, 2, 1, 0] 0 = j := by
  have table : ∀ j < 32, indexFold j [4, 3, 2, 1, 0] 0 = j := by decide
  exact table j bound

end VG.Proof.MillerRabin
