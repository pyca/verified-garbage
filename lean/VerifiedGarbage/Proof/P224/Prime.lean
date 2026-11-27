module

import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Spec.P224
public import VerifiedGarbage.Proof.Framework.IsPrime

/-!
# The P-224 field prime `p = 2^224 - 2^96 + 1` and group order `n` are prime

Pratt certificates (`Proof/Framework/Pratt.lean`), one theorem per prime of
the trees: for `p`, from the factors of `p - 1 = 2^96 (2^128 - 1)` (those of
the Fermat numbers `2^(2^k) + 1`, `k < 7`); for `n`, from the factors of
`n - 1` (PARI/GP's `factor`, recursively). Factors below `2^16` are prime by
trial division (`prime_small`). The group law needs only `p` prime
(`Weierstrass.Good`); the inversion modulo `n` by divsteps needs `n` prime
(`InvSound`).
-/

@[expose] public section

namespace VG.Proof.P224

open VG.Proof.Pratt

/-- The factors below `2^16`, each checked once. -/
theorem small_2 : IsPrime 2 := prime_small _ (by decide +kernel)
theorem small_3 : IsPrime 3 := prime_small _ (by decide +kernel)
theorem small_5 : IsPrime 5 := prime_small _ (by decide +kernel)
theorem small_7 : IsPrime 7 := prime_small _ (by decide +kernel)
theorem small_11 : IsPrime 11 := prime_small _ (by decide +kernel)
theorem small_17 : IsPrime 17 := prime_small _ (by decide +kernel)
theorem small_31 : IsPrime 31 := prime_small _ (by decide +kernel)
theorem small_37 : IsPrime 37 := prime_small _ (by decide +kernel)
theorem small_47 : IsPrime 47 := prime_small _ (by decide +kernel)
theorem small_61 : IsPrime 61 := prime_small _ (by decide +kernel)
theorem small_89 : IsPrime 89 := prime_small _ (by decide +kernel)
theorem small_239 : IsPrime 239 := prime_small _ (by decide +kernel)
theorem small_347 : IsPrime 347 := prime_small _ (by decide +kernel)
theorem small_349 : IsPrime 349 := prime_small _ (by decide +kernel)
theorem small_373 : IsPrime 373 := prime_small _ (by decide +kernel)
theorem small_509 : IsPrime 509 := prime_small _ (by decide +kernel)
theorem small_631 : IsPrime 631 := prime_small _ (by decide +kernel)
theorem small_1303 : IsPrime 1303 := prime_small _ (by decide +kernel)
theorem small_1319 : IsPrime 1319 := prime_small _ (by decide +kernel)
theorem small_2089 : IsPrime 2089 := prime_small _ (by decide +kernel)
theorem small_2153 : IsPrime 2153 := prime_small _ (by decide +kernel)
theorem small_2707 : IsPrime 2707 := prime_small _ (by decide +kernel)
theorem small_10909 : IsPrime 10909 := prime_small _ (by decide +kernel)
theorem small_16657 : IsPrime 16657 := prime_small _ (by decide +kernel)
theorem small_17449 : IsPrime 17449 := prime_small _ (by decide +kernel)
theorem small_20599 : IsPrime 20599 := prime_small _ (by decide +kernel)
theorem small_30859 : IsPrime 30859 := prime_small _ (by decide +kernel)

theorem prime_65537 : IsPrime 65537 := by
  refine prime_of_cert 65537 3 17 (List.replicate 16 2) (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_replicate] at hf
  rcases hf with ⟨-, rfl⟩
  · exact prime_small _ (by decide +kernel)

theorem prime_274177 : IsPrime 274177 := by
  refine prime_of_cert 274177 5 19 [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 17] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_7
  · exact small_17

theorem prime_6700417 : IsPrime 6700417 := by
  refine prime_of_cert 6700417 5 23 [2, 2, 2, 2, 2, 2, 2, 3, 17449] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_17449

theorem prime_166571 : IsPrime 166571 := by
  refine prime_of_cert 166571 2 18 [2, 5, 16657] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_16657

theorem prime_2998279 : IsPrime 2998279 := by
  refine prime_of_cert 2998279 3 22 [2, 3, 3, 166571] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact prime_166571

theorem prime_67280421310721 : IsPrime 67280421310721 := by
  refine prime_of_cert 67280421310721 3 46 [2, 2, 2, 2, 2, 2, 2, 2, 5, 47, 373, 2998279] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_47
  · exact small_373
  · exact prime_2998279

theorem prime_26959946667150639794667015087019630673557916260026308143510066298881 : IsPrime 26959946667150639794667015087019630673557916260026308143510066298881 := by
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

theorem prime_85999 : IsPrime 85999 := by
  refine prime_of_cert 85999 3 17 [2, 3, 11, 1303] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_11
  · exact small_1303

theorem prime_145091 : IsPrime 145091 := by
  refine prime_of_cert 145091 2 18 [2, 5, 11, 1319] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_11
  · exact small_1319

theorem prime_13928737 : IsPrime 13928737 := by
  refine prime_of_cert 13928737 15 24 [2, 2, 2, 2, 2, 3, 145091] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact prime_145091

theorem prime_166823 : IsPrime 166823 := by
  refine prime_of_cert 166823 5 18 [2, 239, 349] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_239
  · exact small_349

theorem prime_87739 : IsPrime 87739 := by
  refine prime_of_cert 87739 7 17 [2, 3, 7, 2089] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_7
  · exact small_2089

theorem prime_11105363 : IsPrime 11105363 := by
  refine prime_of_cert 11105363 2 24 [2, 509, 10909] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_509
  · exact small_10909

theorem prime_821796863 : IsPrime 821796863 := by
  refine prime_of_cert 821796863 5 30 [2, 37, 11105363] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_37
  · exact prime_11105363

theorem prime_432621809776543 : IsPrime 432621809776543 := by
  refine prime_of_cert 432621809776543 3 49 [2, 3, 87739, 821796863] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact prime_87739
  · exact prime_821796863

theorem prime_136401162692544977256234449 : IsPrime 136401162692544977256234449 := by
  refine prime_of_cert 136401162692544977256234449 3 87 [2, 2, 2, 2, 31, 20599, 30859, 432621809776543] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_31
  · exact small_20599
  · exact small_30859
  · exact prime_432621809776543

theorem prime_34646440928557194402992574983797 : IsPrime 34646440928557194402992574983797 := by
  refine prime_of_cert 34646440928557194402992574983797 2 105 [2, 2, 3, 61, 347, 136401162692544977256234449] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_61
  · exact small_347
  · exact prime_136401162692544977256234449

theorem prime_375503554633724504423937478103159147573209 : IsPrime 375503554633724504423937478103159147573209 := by
  refine prime_of_cert 375503554633724504423937478103159147573209 19 139 [2, 2, 2, 3, 2707, 166823, 34646440928557194402992574983797] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_2707
  · exact prime_166823
  · exact prime_34646440928557194402992574983797

theorem prime_50520606258875818707470860153287666700917696099933389351507 : IsPrime 50520606258875818707470860153287666700917696099933389351507 := by
  refine prime_of_cert 50520606258875818707470860153287666700917696099933389351507 2 196 [2, 89, 631, 85999, 13928737, 375503554633724504423937478103159147573209] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_89
  · exact small_631
  · exact prime_85999
  · exact prime_13928737
  · exact prime_375503554633724504423937478103159147573209

theorem prime_26959946667150639794667015087019625940457807714424391721682722368061 : IsPrime 26959946667150639794667015087019625940457807714424391721682722368061 := by
  refine prime_of_cert 26959946667150639794667015087019625940457807714424391721682722368061 2 224 [2, 2, 3, 3, 3, 3, 3, 3, 5, 17, 2153, 50520606258875818707470860153287666700917696099933389351507] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_17
  · exact small_2153
  · exact prime_50520606258875818707470860153287666700917696099933389351507

theorem n_prime : IsPrime Spec.P224.n := by
  rw [show Spec.P224.n = 26959946667150639794667015087019625940457807714424391721682722368061 by decide]
  exact prime_26959946667150639794667015087019625940457807714424391721682722368061

end VG.Proof.P224
