import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Spec.P224

/-!
# The P-224 field prime `p = 2^224 - 2^96 + 1` is prime

A Pratt certificate (`Proof/Framework/Pratt.lean`), one theorem per prime of
the tree, from the factors of `p - 1 = 2^96 (2^128 - 1)` (those of the Fermat
numbers `2^(2^k) + 1`, `k < 7`). Factors below `2^16` are prime by trial
division (`prime_small`). The group law needs only `p` prime
(`Weierstrass.Good`).
-/

namespace VG.Proof.P224

open VG.Proof.Pratt

theorem prime_65537 : Nat.Prime 65537 := by
  refine prime_of_cert 65537 3 17 (List.replicate 16 2) (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_replicate] at hf
  rcases hf with ⟨-, rfl⟩
  · exact prime_small _ (by decide +kernel)

theorem prime_274177 : Nat.Prime 274177 := by
  refine prime_of_cert 274177 5 19 [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 17] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_6700417 : Nat.Prime 6700417 := by
  refine prime_of_cert 6700417 5 23 [2, 2, 2, 2, 2, 2, 2, 3, 17449] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_166571 : Nat.Prime 166571 := by
  refine prime_of_cert 166571 2 18 [2, 5, 16657] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_2998279 : Nat.Prime 2998279 := by
  refine prime_of_cert 2998279 3 22 [2, 3, 3, 166571] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_166571

theorem prime_67280421310721 : Nat.Prime 67280421310721 := by
  refine prime_of_cert 67280421310721 3 46 [2, 2, 2, 2, 2, 2, 2, 2, 5, 47, 373, 2998279] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_2998279

theorem prime_26959946667150639794667015087019630673557916260026308143510066298881 : Nat.Prime 26959946667150639794667015087019630673557916260026308143510066298881 := by
  refine prime_of_cert 26959946667150639794667015087019630673557916260026308143510066298881 22 224 (List.replicate 96 2 ++ [3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721]) (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with ⟨-, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_65537
  · exact prime_274177
  · exact prime_6700417
  · exact prime_67280421310721

theorem p_prime : Nat.Prime Spec.P224.p := by
  rw [show Spec.P224.p = 26959946667150639794667015087019630673557916260026308143510066298881 by decide]
  exact prime_26959946667150639794667015087019630673557916260026308143510066298881

end VG.Proof.P224
