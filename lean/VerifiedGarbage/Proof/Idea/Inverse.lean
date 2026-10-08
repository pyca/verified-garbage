import VerifiedGarbage.Spec.Idea
import VerifiedGarbage.Proof.Framework.Pratt

/-!
# IDEA: the ⊙-inverse by squaring and multiplying

The implementations compute the ⊙-inverse of `a` as `chain a 15`: fifteen
steps of `t := (t ⊙ t) ⊙ a` from `t = a`, which is `a ^ (2¹⁶ - 1)`
(`residue_chain`), `Spec.Idea.inv a` (`chain_inv`). ⊙ multiplies residues
modulo the prime 2¹⁶ + 1 (`residue_mul`), whose primality (`prime`, by a
Pratt certificate) keeps every product nonzero.
-/

namespace VG.Proof.Idea

open VG Spec.Idea

theorem prime : Nat.Prime 65537 :=
  Pratt.prime_of_cert 65537 3 17 (List.replicate 16 2) (by decide) (by decide)
    (fun f hf => by rw [List.eq_of_mem_replicate hf]; exact Pratt.prime_small 2 (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
    (fun f hf => by rw [List.eq_of_mem_replicate hf]; decide +kernel)

theorem residue_le' (a : Word) : residue a ≤ 65536 := by
  unfold residue; split
  · exact Nat.le_refl _
  · exact Nat.le_of_lt a.isLt

theorem residue_pos' (a : Word) : 0 < residue a := by
  unfold residue; split
  · decide
  · rename_i h; exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq h')

theorem residue_ofNat {v : Nat} (h₁ : 1 ≤ v) (h₂ : v ≤ 65536) : residue (BitVec.ofNat 16 v) = v := by
  unfold residue
  split
  · rename_i h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, show (0 : BitVec 16).toNat = 0 from rfl] at this
    omega
  · rename_i h
    have hv : v ≠ 65536 := by rintro rfl; exact h rfl
    simp only [BitVec.toNat_ofNat]; omega

theorem ofNat_residue (a : Word) : BitVec.ofNat 16 (residue a) = a := by
  unfold residue
  split
  · rename_i h; rw [h]; rfl
  · exact (BitVec.ofNat_toNat 16 a).trans (BitVec.setWidth_eq a)

/-- A product of residues is not divisible by 2¹⁶ + 1. -/
theorem mod_pos {x y : Nat} (hx : 0 < x) (hx' : x ≤ 65536) (hy : 0 < y) (hy' : y ≤ 65536) :
    0 < x * y % 65537 := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rcases (Nat.Prime.dvd_mul prime).mp (Nat.dvd_of_mod_eq_zero h) with h | h
  · have := Nat.le_of_dvd hx h; omega
  · have := Nat.le_of_dvd hy h; omega

theorem residue_mul (x y : Word) : residue (mul x y) = residue x * residue y % 65537 := by
  have h := mod_pos (residue_pos' x) (residue_le' x) (residue_pos' y) (residue_le' y)
  exact residue_ofNat h (by omega)

/-- `t := (t ⊙ t) ⊙ a`, `k` times from `t = a`. -/
def chain (a : Word) : Nat → Word
  | 0 => a
  | k + 1 => mul (mul (chain a k) (chain a k)) a

theorem residue_chain (a : Word) (k : Nat) :
    residue (chain a k) = residue a ^ (2 ^ (k + 1) - 1) % 65537 := by
  induction k with
  | zero =>
    simp only [chain, Nat.zero_add, Nat.pow_one, Nat.add_one_sub_one, Nat.pow_one]
    have := residue_le' a; have := residue_pos' a
    omega
  | succ k ih =>
    rw [chain, residue_mul, residue_mul, ih]
    have e : 2 ^ (k + 1 + 1) - 1 = (2 ^ (k + 1) - 1) + (2 ^ (k + 1) - 1) + 1 := by
      rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := k + 1); omega
    rw [e, ← Nat.mul_mod, Nat.mod_mul_mod]
    simp only [Nat.pow_add, Nat.pow_one]

theorem powMod_eq (a e m : Nat) : powMod a e m = a ^ e % m := by
  induction e using Nat.strongRecOn with
  | _ e ih =>
    rw [powMod]
    split
    · rename_i h; subst h; simp
    · rename_i h
      simp only
      rw [ih (e / 2) (by omega), ← Nat.mul_mod, ← Nat.pow_add]
      split
      · rename_i h2
        rw [show e / 2 + e / 2 = e by omega]
      · rename_i h2
        rw [Nat.mod_mul_mod, ← Nat.pow_succ, Nat.succ_eq_add_one, show e / 2 + e / 2 + 1 = e by omega]

theorem chain_inv (a : Word) : chain a 15 = inv a := by
  rw [inv, powMod_eq, ← residue_chain, ofNat_residue]

end VG.Proof.Idea
