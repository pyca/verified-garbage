module

public import VerifiedGarbage.Proof.Weierstrass.Env

/-! # Small linear combinations in Montgomery form -/

@[expose] public section

namespace VG.Proof.Weierstrass.Cms

open VG.Proof.Weierstrass

/-- `k x`, `x` added `k` times. -/
def smulN {F : Type _} [Lean.Grind.CommRing F] : Nat → F → F
  | 0, _ => 0
  | k + 1, x => smulN k x + x

theorem smulN_fin {m : Nat} [NeZero m] : ∀ (k : Nat) (x : Fin m), smulN k x = Fin.ofNat m k * x
  | 0, x => by
    rw [smulN]
    apply Fin.ext
    simp [Fin.val_mul]
  | k + 1, x => by
    rw [smulN, smulN_fin k x, ofNat_add', Lean.Grind.Semiring.right_distrib]
    congr 1
    apply Fin.ext
    simp [Fin.val_mul, Fin.val_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem toM_cms {m : Nat} [NeZero m] (R C A D B : Nat) (hB : B ≤ m) :
    toM m R ((C * A + D * (m - B)) % m) = smulN C (toM m R A) - smulN D (toM m R B) := by
  have e : Fin.ofNat m (D * (m - B)) + Fin.ofNat m D * Fin.ofNat m B = 0 := by
    rw [← ofNat_mul', ← ofNat_add', ← Nat.mul_add, Nat.sub_add_cancel hB]
    apply Fin.ext
    rw [Fin.val_ofNat, Nat.mul_mod_left]
    rfl
  unfold toM
  rw [smulN_fin, smulN_fin, ofNat_mod, ofNat_add', ofNat_mul', ofNat_mul']
  rw [ofNat_mul'] at e
  grind


end VG.Proof.Weierstrass.Cms
