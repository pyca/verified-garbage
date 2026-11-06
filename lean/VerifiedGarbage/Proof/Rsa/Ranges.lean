module

public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA private keys: ranges of the working space

The working space of `Impl/Bignum/Layout.lean` with 16 arrays, as the
private-key functions of every target use it: the slots of its arrays
(`slot_lt`, `slot_mono`, `slot_add`) and an array's byte range (`ar`).
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG VG.Proof.Bignum

theorem slot_lt {w j K : Nat} (h : j < K) : slot w j + 8 * (w + 2) ≤ slot w K := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ K by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- The byte range of array `j`. -/
abbrev ar (w j : Nat) : Nat × Nat := (slot w j, 8 * (w + 2))

theorem slot_mono {w j k : Nat} (h : j ≤ k) : slot w j ≤ slot w k := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) h
  omega

theorem slot_add (w j k : Nat) : slot w (j + k) = slot w j + k * (8 * (w + 2)) := by
  unfold slot; rw [Nat.add_mul]; omega

/-- The low `j` words of a number of `w ≥ j` words. -/
theorem wv_mod (m : Mem) (B : Addr) (e : Nat) {j w : Nat} (hj : j ≤ w) :
    wv m B e w % 2 ^ (64 * j) = wv m B e j := by
  have e1 := wv_add m B e j (w - j)
  rw [show j + (w - j) = w by omega] at e1
  rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wv_lt _ _ _ _)]


end VG.Proof.Rsa
