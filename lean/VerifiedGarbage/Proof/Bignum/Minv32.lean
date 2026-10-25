module

public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `-m⁻¹ mod 2³²` from `-m⁻¹ mod 2⁶⁴`, on any target

The RSA working space's header holds `-m⁻¹ mod 2⁶⁴`; code that reads its low
32 bits has `-m⁻¹ mod 2³²` for `m`'s low 32 bits (`minv_low`).
-/

@[expose] public section

namespace VG.Proof.Bignum.Minv32

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2³²`, for the low digits. -/
theorem minv_low {m minv : Nat} (h : (m * minv + 1) % 2 ^ 64 = 0) :
    (m % 2 ^ 32 * (minv % 2 ^ 32) + 1) % 2 ^ 32 = 0 := by
  have h' : (m * minv + 1) % 2 ^ 32 = 0 := by
    have := Nat.mod_mod_of_dvd (m * minv + 1) (show 2 ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by decide⟩)
    rw [← this, h]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  exact h'

end VG.Proof.Bignum.Minv32
