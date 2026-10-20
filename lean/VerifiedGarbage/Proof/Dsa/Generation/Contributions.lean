module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp

import VerifiedGarbage.Proof.Dsa.Generation.PEncoding
import VerifiedGarbage.Proof.Framework.Omega

/-! # Radix bounds for the accumulated p-candidate hash contributions -/

@[expose] public section
namespace VG.Proof.Dsa.Generation

/-- Add a fixed contribution independently of the accumulator. -/
theorem contribution_fold (f : Nat → Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl (fun a j => a + f j) acc = acc + xs.foldl (fun a j => a + f j) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (acc + f x), ih (f x), Nat.add_assoc]

def contributions (n : Nat) (v : Nat → Nat) (k : Nat) : Nat :=
  (List.range k).foldl (fun a j => a + v j * 2 ^ (j * n)) 0

theorem contributions_zero (n : Nat) (v : Nat → Nat) : contributions n v 0 = 0 := rfl

theorem contributions_succ (n : Nat) (v : Nat → Nat) (k : Nat) :
    contributions n v (k + 1) = contributions n v k + v k * 2 ^ (k * n) := by
  simp only [contributions, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- k complete n-bit hash values occupy strictly fewer than k*n bits plus
one, including when the most significant digest begins with zeroes. -/
theorem contributions_lt (n : Nat) (v : Nat → Nat) (k : Nat)
    (hv : ∀ j < k, v j < 2 ^ n) : contributions n v k < 2 ^ (k * n) := by
  induction k with
  | zero => simp [contributions_zero]
  | succ k ih =>
    have hlo := ih (fun j hj => hv j (by omega))
    have hhi := hv k (by omega)
    have hmul := Nat.mul_le_mul_right (2 ^ (k * n)) (show v k + 1 ≤ 2 ^ n by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    rw [contributions_succ, Nat.add_mul, Nat.one_mul, Nat.pow_add]
    have hcomm : 2 ^ (k * n) * 2 ^ n = 2 ^ n * 2 ^ (k * n) := Nat.mul_comm _ _
    omega

/-- The range fold can change its function outside the visited indices. -/
theorem contribution_fold_congr (xs : List Nat) (f g : Nat → Nat)
    (he : ∀ j ∈ xs, f j = g j) (acc : Nat) :
    xs.foldl (fun a j => a + f j) acc = xs.foldl (fun a j => a + g j) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons j xs ih =>
    simp only [List.foldl_cons]
    rw [he j (by simp)]
    exact ih (fun k hk => he k (List.mem_cons_of_mem j hk)) _

/-- The specification truncates only the last contribution. This equals
truncating the complete radix assembly at its final partial digit. -/
theorem contributions_cut (n b count : Nat) (v : Nat → Nat)
    (hv : ∀ j < count, v j < 2 ^ n) :
    (List.range (count + 1)).foldl (fun a j =>
      a + (if j == count then v j % 2 ^ b else v j) * 2 ^ (j * n)) 0 =
        contributions n v (count + 1) % (2 ^ (count * n) * 2 ^ b) := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [beq_self_eq_true, ite_true]
  have hp : (List.range count).foldl (fun a j =>
      a + (if j == count then v j % 2 ^ b else v j) * 2 ^ (j * n)) 0 = contributions n v count := by
    apply contribution_fold_congr
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [beq_eq_false_iff_ne.mpr (by omega : j ≠ count), Bool.false_eq_true, ite_false]
  rw [hp, contributions_succ, radix_join_mod (contributions_lt n v count hv)]

end VG.Proof.Dsa.Generation
