module

import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Spec.BrainpoolP384r1
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Prime.Defs
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# The brainpoolP384r1 field prime is prime

Pratt certificates (`Proof/Framework/Pratt.lean`) for RFC 5639's `p` and
`q` (here `n`), one theorem per prime of each tree, from the factors of
`p - 1` and `n - 1`. Factors below `2^16` are prime by trial division
(`prime_small`). The group law needs only `p` prime (`Weierstrass.Good`);
the inversions modulo `n` by divsteps need `n` prime.
-/

@[expose] public section

namespace VG.Proof.BrainpoolP384r1

open VG.Proof.Pratt

theorem small_2 : Nat.Prime 2 := prime_small _ (by decide +kernel)
theorem small_3 : Nat.Prime 3 := prime_small _ (by decide +kernel)
theorem small_5 : Nat.Prime 5 := prime_small _ (by decide +kernel)
theorem small_7 : Nat.Prime 7 := prime_small _ (by decide +kernel)
theorem small_11 : Nat.Prime 11 := prime_small _ (by decide +kernel)
theorem small_13 : Nat.Prime 13 := prime_small _ (by decide +kernel)
theorem small_17 : Nat.Prime 17 := prime_small _ (by decide +kernel)
theorem small_29 : Nat.Prime 29 := prime_small _ (by decide +kernel)
theorem small_41 : Nat.Prime 41 := prime_small _ (by decide +kernel)
theorem small_43 : Nat.Prime 43 := prime_small _ (by decide +kernel)
theorem small_67 : Nat.Prime 67 := prime_small _ (by decide +kernel)
theorem small_71 : Nat.Prime 71 := prime_small _ (by decide +kernel)
theorem small_73 : Nat.Prime 73 := prime_small _ (by decide +kernel)
theorem small_79 : Nat.Prime 79 := prime_small _ (by decide +kernel)
theorem small_83 : Nat.Prime 83 := prime_small _ (by decide +kernel)
theorem small_89 : Nat.Prime 89 := prime_small _ (by decide +kernel)
theorem small_227 : Nat.Prime 227 := prime_small _ (by decide +kernel)
theorem small_251 : Nat.Prime 251 := prime_small _ (by decide +kernel)
theorem small_283 : Nat.Prime 283 := prime_small _ (by decide +kernel)
theorem small_337 : Nat.Prime 337 := prime_small _ (by decide +kernel)
theorem small_1093 : Nat.Prime 1093 := prime_small _ (by decide +kernel)
theorem small_1423 : Nat.Prime 1423 := prime_small _ (by decide +kernel)
theorem small_1777 : Nat.Prime 1777 := prime_small _ (by decide +kernel)
theorem small_1877 : Nat.Prime 1877 := prime_small _ (by decide +kernel)
theorem small_2543 : Nat.Prime 2543 := prime_small _ (by decide +kernel)
theorem small_3037 : Nat.Prime 3037 := prime_small _ (by decide +kernel)
theorem small_3607 : Nat.Prime 3607 := prime_small _ (by decide +kernel)
theorem small_9839 : Nat.Prime 9839 := prime_small _ (by decide +kernel)
theorem small_10453 : Nat.Prime 10453 := prime_small _ (by decide +kernel)
theorem small_11131 : Nat.Prime 11131 := prime_small _ (by decide +kernel)
theorem small_11393 : Nat.Prime 11393 := prime_small _ (by decide +kernel)
theorem small_37967 : Nat.Prime 37967 := prime_small _ (by decide +kernel)
theorem small_19 : Nat.Prime 19 := prime_small _ (by decide +kernel)
theorem small_53 : Nat.Prime 53 := prime_small _ (by decide +kernel)
theorem small_59 : Nat.Prime 59 := prime_small _ (by decide +kernel)
theorem small_103 : Nat.Prime 103 := prime_small _ (by decide +kernel)
theorem small_109 : Nat.Prime 109 := prime_small _ (by decide +kernel)
theorem small_179 : Nat.Prime 179 := prime_small _ (by decide +kernel)
theorem small_241 : Nat.Prime 241 := prime_small _ (by decide +kernel)
theorem small_347 : Nat.Prime 347 := prime_small _ (by decide +kernel)
theorem small_349 : Nat.Prime 349 := prime_small _ (by decide +kernel)
theorem small_617 : Nat.Prime 617 := prime_small _ (by decide +kernel)
theorem small_1049 : Nat.Prime 1049 := prime_small _ (by decide +kernel)
theorem small_1709 : Nat.Prime 1709 := prime_small _ (by decide +kernel)
theorem small_2083 : Nat.Prime 2083 := prime_small _ (by decide +kernel)
theorem small_2377 : Nat.Prime 2377 := prime_small _ (by decide +kernel)
theorem small_2593 : Nat.Prime 2593 := prime_small _ (by decide +kernel)
theorem small_4273 : Nat.Prime 4273 := prime_small _ (by decide +kernel)
theorem small_5413 : Nat.Prime 5413 := prime_small _ (by decide +kernel)
theorem small_5743 : Nat.Prime 5743 := prime_small _ (by decide +kernel)
theorem small_6997 : Nat.Prime 6997 := prime_small _ (by decide +kernel)
theorem small_9341 : Nat.Prime 9341 := prime_small _ (by decide +kernel)
theorem small_18947 : Nat.Prime 18947 := prime_small _ (by decide +kernel)
theorem small_28817 : Nat.Prime 28817 := prime_small _ (by decide +kernel)
theorem small_43397 : Nat.Prime 43397 := prime_small _ (by decide +kernel)
theorem small_60901 : Nat.Prime 60901 := prime_small _ (by decide +kernel)

theorem prime_734647 : Nat.Prime 734647 := by
  refine prime_of_cert 734647 3 20 [2, 3, 11, 11131] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_11
  · exact small_11131

theorem prime_78713 : Nat.Prime 78713 := by
  refine prime_of_cert 78713 3 17 [2, 2, 2, 9839] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_9839

theorem prime_157427 : Nat.Prime 157427 := by
  refine prime_of_cert 157427 2 18 [2, 78713] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact small_2
  · exact prime_78713

theorem prime_27093605140967 : Nat.Prime 27093605140967 := by
  refine prime_of_cert 27093605140967 5 45 [2, 7, 13, 83, 11393, 157427] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_7
  · exact small_13
  · exact small_83
  · exact small_11393
  · exact prime_157427

theorem prime_97151 : Nat.Prime 97151 := by
  refine prime_of_cert 97151 13 17 [2, 5, 5, 29, 67] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_29
  · exact small_67

theorem prime_59016512273 : Nat.Prime 59016512273 := by
  refine prime_of_cert 59016512273 3 36 [2, 2, 2, 2, 37967, 97151] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_37967
  · exact prime_97151

theorem prime_3012146720727260651 : Nat.Prime 3012146720727260651 := by
  refine prime_of_cert 3012146720727260651 13 62 [2, 5, 5, 283, 3607, 59016512273] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_283
  · exact small_3607
  · exact prime_59016512273

theorem prime_868583 : Nat.Prime 868583 := by
  refine prime_of_cert 868583 5 20 [2, 11, 13, 3037] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_11
  · exact small_13
  · exact small_3037

theorem prime_1898722439 : Nat.Prime 1898722439 := by
  refine prime_of_cert 1898722439 11 31 [2, 1093, 868583] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_1093
  · exact prime_868583

theorem prime_123606883 : Nat.Prime 123606883 := by
  refine prime_of_cert 123606883 2 27 [2, 3, 3, 7, 41, 71, 337] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_7
  · exact small_41
  · exact small_71
  · exact small_337

theorem prime_13843970897 : Nat.Prime 13843970897 := by
  refine prime_of_cert 13843970897 5 34 [2, 2, 2, 2, 7, 123606883] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact prime_123606883

theorem prime_8076987940436711 : Nat.Prime 8076987940436711 := by
  refine prime_of_cert 8076987940436711 7 53 [2, 5, 41, 1423, 13843970897] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_41
  · exact small_1423
  · exact prime_13843970897

theorem prime_726928914639303991 : Nat.Prime 726928914639303991 := by
  refine prime_of_cert 726928914639303991 3 60 [2, 3, 3, 5, 8076987940436711] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact prime_8076987940436711

theorem prime_12811352796235023217778801482819 : Nat.Prime 12811352796235023217778801482819 := by
  refine prime_of_cert 12811352796235023217778801482819 2 104 [2, 3, 7, 13, 17, 1898722439, 726928914639303991] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_7
  · exact small_13
  · exact small_17
  · exact prime_1898722439
  · exact prime_726928914639303991

theorem prime_991057 : Nat.Prime 991057 := by
  refine prime_of_cert 991057 10 20 [2, 2, 2, 2, 3, 11, 1877] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_11
  · exact small_1877

theorem prime_95959 : Nat.Prime 95959 := by
  refine prime_of_cert 95959 3 17 [2, 3, 3, 3, 1777] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_1777

theorem prime_2663886769 : Nat.Prime 2663886769 := by
  refine prime_of_cert 2663886769 7 32 [2, 2, 2, 2, 3, 41, 67, 89, 227] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_41
  · exact small_67
  · exact small_89
  · exact small_227

theorem prime_7057776167979264311 : Nat.Prime 7057776167979264311 := by
  refine prime_of_cert 7057776167979264311 11 63 [2, 5, 11, 251, 95959, 2663886769] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_11
  · exact small_251
  · exact prime_95959
  · exact prime_2663886769

theorem prime_9511259360250244436150360929400467 : Nat.Prime 9511259360250244436150360929400467 := by
  refine prime_of_cert 9511259360250244436150360929400467 2 113 [2, 3, 3, 3, 3, 11, 73, 10453, 991057, 7057776167979264311] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_11
  · exact small_73
  · exact small_10453
  · exact prime_991057
  · exact prime_7057776167979264311

theorem prime_13857381403312519376221497559214358876512960238914501360589056738895920081 : Nat.Prime 13857381403312519376221497559214358876512960238914501360589056738895920081 := by
  refine prime_of_cert 13857381403312519376221497559214358876512960238914501360589056738895920081 3 243 [2, 2, 2, 2, 5, 13, 43, 2543, 12811352796235023217778801482819, 9511259360250244436150360929400467] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_13
  · exact small_43
  · exact small_2543
  · exact prime_12811352796235023217778801482819
  · exact prime_9511259360250244436150360929400467

theorem prime_21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 : Nat.Prime 21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 := by
  refine prime_of_cert 21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 3 384 [2, 3, 5, 11, 79, 734647, 27093605140967, 3012146720727260651, 13857381403312519376221497559214358876512960238914501360589056738895920081] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_11
  · exact small_79
  · exact prime_734647
  · exact prime_27093605140967
  · exact prime_3012146720727260651
  · exact prime_13857381403312519376221497559214358876512960238914501360589056738895920081

theorem p_prime : Nat.Prime Spec.BrainpoolP384r1.p := by
  rw [show Spec.BrainpoolP384r1.p = 21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 by decide +kernel]
  exact prime_21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331

theorem prime_4977439 : Nat.Prime 4977439 := by
  refine prime_of_cert 4977439 6 23 [2, 3, 349, 2377] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_349
  · exact small_2377

theorem prime_657021949 : Nat.Prime 657021949 := by
  refine prime_of_cert 657021949 2 30 [2, 2, 3, 11, 4977439] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_11
  · exact prime_4977439

theorem prime_124822877 : Nat.Prime 124822877 := by
  refine prime_of_cert 124822877 2 27 [2, 2, 67, 109, 4273] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_67
  · exact small_109
  · exact small_4273

theorem prime_119087 : Nat.Prime 119087 := by
  refine prime_of_cert 119087 5 17 [2, 11, 5413] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_11
  · exact small_5413

theorem prime_27678676889 : Nat.Prime 27678676889 := by
  refine prime_of_cert 27678676889 6 35 [2, 2, 2, 17, 1709, 119087] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_17
  · exact small_1709
  · exact prime_119087

theorem prime_288135026414491 : Nat.Prime 288135026414491 := by
  refine prime_of_cert 288135026414491 2 49 [2, 3, 5, 347, 27678676889] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_347
  · exact prime_27678676889

theorem prime_8067780739605749 : Nat.Prime 8067780739605749 := by
  refine prime_of_cert 8067780739605749 3 53 [2, 2, 7, 288135026414491] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_7
  · exact prime_288135026414491

theorem prime_53014379452169 : Nat.Prime 53014379452169 := by
  refine prime_of_cert 53014379452169 3 46 [2, 2, 2, 5743, 18947, 60901] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5743
  · exact small_18947
  · exact small_60901

theorem prime_1866961 : Nat.Prime 1866961 := by
  refine prime_of_cert 1866961 13 21 [2, 2, 2, 2, 3, 3, 5, 2593] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_2593

theorem prime_11201767 : Nat.Prime 11201767 := by
  refine prime_of_cert 11201767 3 24 [2, 3, 1866961] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact prime_1866961

theorem prime_1559777 : Nat.Prime 1559777 := by
  refine prime_of_cert 1559777 3 21 [2, 2, 2, 2, 2, 79, 617] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_79
  · exact small_617

theorem prime_11594917 : Nat.Prime 11594917 := by
  refine prime_of_cert 11594917 5 24 [2, 2, 3, 3, 53, 59, 103] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_53
  · exact small_59
  · exact small_103

theorem prime_5071793 : Nat.Prime 5071793 := by
  refine prime_of_cert 5071793 3 23 [2, 2, 2, 2, 11, 28817] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_11
  · exact small_28817

theorem prime_11543603 : Nat.Prime 11543603 := by
  refine prime_of_cert 11543603 2 24 [2, 7, 19, 43397] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_7
  · exact small_19
  · exact small_43397

theorem prime_1454493979 : Nat.Prime 1454493979 := by
  refine prime_of_cert 1454493979 7 31 [2, 3, 3, 7, 11543603] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_7
  · exact prime_11543603

theorem prime_2520431 : Nat.Prime 2520431 := by
  refine prime_of_cert 2520431 7 22 [2, 5, 11, 11, 2083] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_11
  · exact small_11
  · exact small_2083

theorem prime_49393939847159 : Nat.Prime 49393939847159 := by
  refine prime_of_cert 49393939847159 13 46 [2, 1049, 9341, 2520431] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_1049
  · exact small_9341
  · exact prime_2520431

theorem prime_2788900573532341797131599550190476443808598899 : Nat.Prime 2788900573532341797131599550190476443808598899 := by
  refine prime_of_cert 2788900573532341797131599550190476443808598899 2 151 [2, 7, 179, 241, 1093, 5071793, 11594917, 1454493979, 49393939847159] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_7
  · exact small_179
  · exact small_241
  · exact small_1093
  · exact prime_5071793
  · exact prime_11594917
  · exact prime_1454493979
  · exact prime_49393939847159

theorem prime_669909697361913545660898382546007419518544524592370543 : Nat.Prime 669909697361913545660898382546007419518544524592370543 := by
  refine prime_of_cert 669909697361913545660898382546007419518544524592370543 5 179 [2, 7, 11, 1559777, 2788900573532341797131599550190476443808598899] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_7
  · exact small_11
  · exact prime_1559777
  · exact prime_2788900573532341797131599550190476443808598899

theorem prime_90050068090664042551646936303486902724615855323314057604193773 : Nat.Prime 90050068090664042551646936303486902724615855323314057604193773 := by
  refine prime_of_cert 90050068090664042551646936303486902724615855323314057604193773 2 206 [2, 2, 3, 11201767, 669909697361913545660898382546007419518544524592370543] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact prime_11201767
  · exact prime_669909697361913545660898382546007419518544524592370543

theorem prime_21659270770119316173069236842332604979796116387017648600075645274821611501358515537962695117368903252229601718723941 : Nat.Prime 21659270770119316173069236842332604979796116387017648600075645274821611501358515537962695117368903252229601718723941 := by
  refine prime_of_cert 21659270770119316173069236842332604979796116387017648600075645274821611501358515537962695117368903252229601718723941 2 384 [2, 2, 5, 7, 7, 6997, 124822877, 657021949, 53014379452169, 8067780739605749, 90050068090664042551646936303486902724615855323314057604193773] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_7
  · exact small_7
  · exact small_6997
  · exact prime_124822877
  · exact prime_657021949
  · exact prime_53014379452169
  · exact prime_8067780739605749
  · exact prime_90050068090664042551646936303486902724615855323314057604193773

theorem n_prime : Nat.Prime Spec.BrainpoolP384r1.n := by
  rw [show Spec.BrainpoolP384r1.n = 21659270770119316173069236842332604979796116387017648600075645274821611501358515537962695117368903252229601718723941 by decide +kernel]
  exact prime_21659270770119316173069236842332604979796116387017648600075645274821611501358515537962695117368903252229601718723941

end VG.Proof.BrainpoolP384r1
