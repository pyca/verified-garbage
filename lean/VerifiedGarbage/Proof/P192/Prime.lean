import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Spec.P192

/-!
# The P-192 field prime is prime

A Pratt certificate (`Proof/Framework/Pratt.lean`) for `p = 2^192 - 2^64 - 1`,
one theorem per prime of the tree, from the factors of `p - 1`. Factors
below `2^16` are prime by trial division (`prime_small`). The group law needs
only `p` prime (`Weierstrass.Good`).
-/

namespace VG.Proof.P192

open VG.Proof.Pratt

theorem small_2 : Nat.Prime 2 := prime_small _ (by decide +kernel)
theorem small_3 : Nat.Prime 3 := prime_small _ (by decide +kernel)
theorem small_5 : Nat.Prime 5 := prime_small _ (by decide +kernel)
theorem small_7 : Nat.Prime 7 := prime_small _ (by decide +kernel)
theorem small_11 : Nat.Prime 11 := prime_small _ (by decide +kernel)
theorem small_17 : Nat.Prime 17 := prime_small _ (by decide +kernel)
theorem small_19 : Nat.Prime 19 := prime_small _ (by decide +kernel)
theorem small_37 : Nat.Prime 37 := prime_small _ (by decide +kernel)
theorem small_41 : Nat.Prime 41 := prime_small _ (by decide +kernel)
theorem small_43 : Nat.Prime 43 := prime_small _ (by decide +kernel)
theorem small_59 : Nat.Prime 59 := prime_small _ (by decide +kernel)
theorem small_61 : Nat.Prime 61 := prime_small _ (by decide +kernel)
theorem small_163 : Nat.Prime 163 := prime_small _ (by decide +kernel)
theorem small_191 : Nat.Prime 191 := prime_small _ (by decide +kernel)
theorem small_229 : Nat.Prime 229 := prime_small _ (by decide +kernel)
theorem small_283 : Nat.Prime 283 := prime_small _ (by decide +kernel)
theorem small_607 : Nat.Prime 607 := prime_small _ (by decide +kernel)
theorem small_631 : Nat.Prime 631 := prime_small _ (by decide +kernel)
theorem small_907 : Nat.Prime 907 := prime_small _ (by decide +kernel)
theorem small_2477 : Nat.Prime 2477 := prime_small _ (by decide +kernel)
theorem small_54251 : Nat.Prime 54251 := prime_small _ (by decide +kernel)

theorem prime_149309 : Nat.Prime 149309 := by
  refine prime_of_cert 149309 2 18 [2, 2, 163, 229] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_163
  · exact small_229

theorem prime_379787 : Nat.Prime 379787 := by
  refine prime_of_cert 379787 2 19 [2, 11, 61, 283] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_11
  · exact small_61
  · exact small_283

theorem prime_11393611 : Nat.Prime 11393611 := by
  refine prime_of_cert 11393611 10 24 [2, 3, 5, 379787] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact prime_379787

theorem prime_275729 : Nat.Prime 275729 := by
  refine prime_of_cert 275729 3 19 [2, 2, 2, 2, 19, 907] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_19
  · exact small_907

theorem prime_108341181769254293 : Nat.Prime 108341181769254293 := by
  refine prime_of_cert 108341181769254293 2 57 [2, 2, 17, 43, 2477, 54251, 275729] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_17
  · exact small_43
  · exact small_2477
  · exact small_54251
  · exact prime_275729

theorem prime_723127 : Nat.Prime 723127 := by
  refine prime_of_cert 723127 3 20 [2, 3, 191, 631] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_191
  · exact small_631

theorem prime_8413201 : Nat.Prime 8413201 := by
  refine prime_of_cert 8413201 29 24 [2, 2, 2, 2, 3, 3, 3, 5, 5, 19, 41] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_5
  · exact small_19
  · exact small_41

theorem prime_252396031 : Nat.Prime 252396031 := by
  refine prime_of_cert 252396031 3 28 [2, 3, 5, 8413201] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact prime_8413201

theorem prime_455827231987 : Nat.Prime 455827231987 := by
  refine prime_of_cert 455827231987 2 39 [2, 3, 7, 43, 252396031] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_7
  · exact small_43
  · exact prime_252396031

theorem prime_5933177618131140283 : Nat.Prime 5933177618131140283 := by
  refine prime_of_cert 5933177618131140283 2 63 [2, 3, 3, 723127, 455827231987] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact prime_723127
  · exact prime_455827231987

theorem prime_288626509448065367648032903 : Nat.Prime 288626509448065367648032903 := by
  refine prime_of_cert 288626509448065367648032903 6 88 [2, 3, 19, 19, 37, 607, 5933177618131140283] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_19
  · exact small_19
  · exact small_37
  · exact small_607
  · exact prime_5933177618131140283

theorem prime_6277101735386680763835789423207666416083908700390324961279 : Nat.Prime 6277101735386680763835789423207666416083908700390324961279 := by
  refine prime_of_cert 6277101735386680763835789423207666416083908700390324961279 11 192 [2, 59, 149309, 11393611, 108341181769254293, 288626509448065367648032903] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_59
  · exact prime_149309
  · exact prime_11393611
  · exact prime_108341181769254293
  · exact prime_288626509448065367648032903

theorem p_prime : Nat.Prime Spec.P192.p := by
  rw [show Spec.P192.p = 6277101735386680763835789423207666416083908700390324961279 by decide +kernel]
  exact prime_6277101735386680763835789423207666416083908700390324961279

end VG.Proof.P192
