import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Spec.P521

/-!
# The P-521 field prime `p = 2^521 - 1` and group order `n` are prime

Pratt certificates (`Proof/Framework/Pratt.lean`), one theorem per prime of
the trees: for `p`, from the factors of `2^520 - 1` (those of the cyclotomic
numbers `Φ_d(2)` for `d ∣ 520`); for `n`, from the factors of `n - 1`, found by
PARI/GP and, for the 91-digit cofactor in the tree of its 118-digit factor,
by FactorDB, and each checked here by the kernel like every other factor. Factors below `2^16` are prime by trial division
(`prime_small`). The group law needs only `p` prime (`Weierstrass.Good`).
-/

namespace VG.Proof.P521

open VG.Proof.Pratt

theorem small_2 : Nat.Prime 2 := prime_small _ (by decide +kernel)
theorem small_3 : Nat.Prime 3 := prime_small _ (by decide +kernel)
theorem small_5 : Nat.Prime 5 := prime_small _ (by decide +kernel)
theorem small_7 : Nat.Prime 7 := prime_small _ (by decide +kernel)
theorem small_11 : Nat.Prime 11 := prime_small _ (by decide +kernel)
theorem small_13 : Nat.Prime 13 := prime_small _ (by decide +kernel)
theorem small_17 : Nat.Prime 17 := prime_small _ (by decide +kernel)
theorem small_19 : Nat.Prime 19 := prime_small _ (by decide +kernel)
theorem small_31 : Nat.Prime 31 := prime_small _ (by decide +kernel)
theorem small_37 : Nat.Prime 37 := prime_small _ (by decide +kernel)
theorem small_41 : Nat.Prime 41 := prime_small _ (by decide +kernel)
theorem small_53 : Nat.Prime 53 := prime_small _ (by decide +kernel)
theorem small_59 : Nat.Prime 59 := prime_small _ (by decide +kernel)
theorem small_61 : Nat.Prime 61 := prime_small _ (by decide +kernel)
theorem small_79 : Nat.Prime 79 := prime_small _ (by decide +kernel)
theorem small_97 : Nat.Prime 97 := prime_small _ (by decide +kernel)
theorem small_109 : Nat.Prime 109 := prime_small _ (by decide +kernel)
theorem small_127 : Nat.Prime 127 := prime_small _ (by decide +kernel)
theorem small_131 : Nat.Prime 131 := prime_small _ (by decide +kernel)
theorem small_151 : Nat.Prime 151 := prime_small _ (by decide +kernel)
theorem small_157 : Nat.Prime 157 := prime_small _ (by decide +kernel)
theorem small_191 : Nat.Prime 191 := prime_small _ (by decide +kernel)
theorem small_193 : Nat.Prime 193 := prime_small _ (by decide +kernel)
theorem small_223 : Nat.Prime 223 := prime_small _ (by decide +kernel)
theorem small_229 : Nat.Prime 229 := prime_small _ (by decide +kernel)
theorem small_233 : Nat.Prime 233 := prime_small _ (by decide +kernel)
theorem small_263 : Nat.Prime 263 := prime_small _ (by decide +kernel)
theorem small_277 : Nat.Prime 277 := prime_small _ (by decide +kernel)
theorem small_281 : Nat.Prime 281 := prime_small _ (by decide +kernel)
theorem small_311 : Nat.Prime 311 := prime_small _ (by decide +kernel)
theorem small_317 : Nat.Prime 317 := prime_small _ (by decide +kernel)
theorem small_347 : Nat.Prime 347 := prime_small _ (by decide +kernel)
theorem small_397 : Nat.Prime 397 := prime_small _ (by decide +kernel)
theorem small_421 : Nat.Prime 421 := prime_small _ (by decide +kernel)
theorem small_521 : Nat.Prime 521 := prime_small _ (by decide +kernel)
theorem small_547 : Nat.Prime 547 := prime_small _ (by decide +kernel)
theorem small_683 : Nat.Prime 683 := prime_small _ (by decide +kernel)
theorem small_811 : Nat.Prime 811 := prime_small _ (by decide +kernel)
theorem small_877 : Nat.Prime 877 := prime_small _ (by decide +kernel)
theorem small_1051 : Nat.Prime 1051 := prime_small _ (by decide +kernel)
theorem small_1187 : Nat.Prime 1187 := prime_small _ (by decide +kernel)
theorem small_1283 : Nat.Prime 1283 := prime_small _ (by decide +kernel)
theorem small_1381 : Nat.Prime 1381 := prime_small _ (by decide +kernel)
theorem small_1433 : Nat.Prime 1433 := prime_small _ (by decide +kernel)
theorem small_1543 : Nat.Prime 1543 := prime_small _ (by decide +kernel)
theorem small_1613 : Nat.Prime 1613 := prime_small _ (by decide +kernel)
theorem small_1663 : Nat.Prime 1663 := prime_small _ (by decide +kernel)
theorem small_2437 : Nat.Prime 2437 := prime_small _ (by decide +kernel)
theorem small_2731 : Nat.Prime 2731 := prime_small _ (by decide +kernel)
theorem small_3191 : Nat.Prime 3191 := prime_small _ (by decide +kernel)
theorem small_5449 : Nat.Prime 5449 := prime_small _ (by decide +kernel)
theorem small_6043 : Nat.Prime 6043 := prime_small _ (by decide +kernel)
theorem small_8191 : Nat.Prime 8191 := prime_small _ (by decide +kernel)
theorem small_9227 : Nat.Prime 9227 := prime_small _ (by decide +kernel)
theorem small_10861 : Nat.Prime 10861 := prime_small _ (by decide +kernel)
theorem small_14461 : Nat.Prime 14461 := prime_small _ (by decide +kernel)
theorem small_15601 : Nat.Prime 15601 := prime_small _ (by decide +kernel)
theorem small_17293 : Nat.Prime 17293 := prime_small _ (by decide +kernel)
theorem small_17467 : Nat.Prime 17467 := prime_small _ (by decide +kernel)
theorem small_20341 : Nat.Prime 20341 := prime_small _ (by decide +kernel)
theorem small_23609 : Nat.Prime 23609 := prime_small _ (by decide +kernel)
theorem small_28793 : Nat.Prime 28793 := prime_small _ (by decide +kernel)
theorem small_42641 : Nat.Prime 42641 := prime_small _ (by decide +kernel)
theorem small_49481 : Nat.Prime 49481 := prime_small _ (by decide +kernel)
theorem small_51481 : Nat.Prime 51481 := prime_small _ (by decide +kernel)
theorem small_61681 : Nat.Prime 61681 := prime_small _ (by decide +kernel)

theorem prime_409891 : Nat.Prime 409891 := by
  refine prime_of_cert 409891 14 19 [2, 3, 5, 13, 1051] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_13
  · exact small_1051

theorem prime_858001 : Nat.Prime 858001 := by
  refine prime_of_cert 858001 17 20 [2, 2, 2, 2, 3, 5, 5, 5, 11, 13] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_11
  · exact small_13

theorem prime_5746001 : Nat.Prime 5746001 := by
  refine prime_of_cert 5746001 15 23 [2, 2, 2, 2, 5, 5, 5, 13, 13, 17] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_13
  · exact small_13
  · exact small_17

theorem prime_7623851 : Nat.Prime 7623851 := by
  refine prime_of_cert 7623851 6 23 [2, 5, 5, 13, 37, 317] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_13
  · exact small_37
  · exact small_317

theorem prime_34110701 : Nat.Prime 34110701 := by
  refine prime_of_cert 34110701 15 26 [2, 2, 5, 5, 13, 19, 1381] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_13
  · exact small_19
  · exact small_1381

theorem prime_308761441 : Nat.Prime 308761441 := by
  refine prime_of_cert 308761441 17 29 [2, 2, 2, 2, 2, 3, 5, 13, 49481] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_13
  · exact small_49481

theorem prime_2400573761 : Nat.Prime 2400573761 := by
  refine prime_of_cert 2400573761 3 32 [2, 2, 2, 2, 2, 2, 5, 13, 347, 1663] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_13
  · exact small_347
  · exact small_1663

theorem prime_2995763 : Nat.Prime 2995763 := by
  refine prime_of_cert 2995763 2 22 [2, 7, 7, 7, 11, 397] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_7
  · exact small_7
  · exact small_7
  · exact small_11
  · exact small_397

theorem prime_65427463921 : Nat.Prime 65427463921 := by
  refine prime_of_cert 65427463921 17 36 [2, 2, 2, 2, 3, 5, 7, 13, 2995763] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_7
  · exact small_13
  · exact prime_2995763

theorem prime_108140989558681 : Nat.Prime 108140989558681 := by
  refine prime_of_cert 108140989558681 17 47 [2, 2, 2, 3, 3, 5, 13, 683, 1433, 23609] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_13
  · exact small_683
  · exact small_1433
  · exact small_23609

theorem prime_8620289 : Nat.Prime 8620289 := by
  refine prime_of_cert 8620289 3 24 [2, 2, 2, 2, 2, 2, 2, 2, 151, 223] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_151
  · exact small_223

theorem prime_2534364967 : Nat.Prime 2534364967 := by
  refine prime_of_cert 2534364967 3 32 [2, 3, 7, 7, 8620289] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_7
  · exact small_7
  · exact prime_8620289

theorem prime_145295143558111 : Nat.Prime 145295143558111 := by
  refine prime_of_cert 145295143558111 7 48 [2, 3, 3, 5, 7, 7, 13, 2534364967] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_7
  · exact small_7
  · exact small_13
  · exact prime_2534364967

theorem prime_9211861 : Nat.Prime 9211861 := by
  refine prime_of_cert 9211861 2 24 [2, 2, 3, 3, 3, 5, 7, 2437] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_7
  · exact small_2437

theorem prime_24098228377 : Nat.Prime 24098228377 := by
  refine prime_of_cert 24098228377 7 35 [2, 2, 2, 3, 109, 9211861] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_109
  · exact prime_9211861

theorem prime_674750394557 : Nat.Prime 674750394557 := by
  refine prime_of_cert 674750394557 2 40 [2, 2, 7, 24098228377] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_7
  · exact prime_24098228377

theorem prime_361725589517273017 : Nat.Prime 361725589517273017 := by
  refine prime_of_cert 361725589517273017 17 59 [2, 2, 2, 3, 7, 3191, 674750394557] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_7
  · exact small_3191
  · exact prime_674750394557

theorem prime_173308343918874810521923841 : Nat.Prime 173308343918874810521923841 := by
  refine prime_of_cert 173308343918874810521923841 3 88 [2, 2, 2, 2, 2, 2, 2, 2, 5, 13, 28793, 361725589517273017] (by decide) (by decide +kernel) ?_
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
  · exact small_13
  · exact small_28793
  · exact prime_361725589517273017

theorem prime_6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 : Nat.Prime 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 := by
  refine prime_of_cert 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 3 521 [2, 3, 5, 5, 11, 17, 31, 41, 53, 131, 157, 521, 1613, 2731, 8191, 42641, 51481, 61681, 409891, 858001, 5746001, 7623851, 34110701, 308761441, 2400573761, 65427463921, 108140989558681, 145295143558111, 173308343918874810521923841] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_5
  · exact small_11
  · exact small_17
  · exact small_31
  · exact small_41
  · exact small_53
  · exact small_131
  · exact small_157
  · exact small_521
  · exact small_1613
  · exact small_2731
  · exact small_8191
  · exact small_42641
  · exact small_51481
  · exact small_61681
  · exact prime_409891
  · exact prime_858001
  · exact prime_5746001
  · exact prime_7623851
  · exact prime_34110701
  · exact prime_308761441
  · exact prime_2400573761
  · exact prime_65427463921
  · exact prime_108140989558681
  · exact prime_145295143558111
  · exact prime_173308343918874810521923841

theorem p_prime : Nat.Prime Spec.P521.p := by
  rw [show Spec.P521.p =
    6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 by decide +kernel]
  exact prime_6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151

theorem prime_1458105463 : Nat.Prime 1458105463 := by
  refine prime_of_cert 1458105463 3 31 [2, 3, 3, 3, 3, 3, 11, 311, 877] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_11
  · exact small_311
  · exact small_877

theorem prime_186406729 : Nat.Prime 186406729 := by
  refine prime_of_cert 186406729 7 28 [2, 2, 2, 3, 61, 157, 811] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_61
  · exact small_157
  · exact small_811

theorem prime_88599952463812275001 : Nat.Prime 88599952463812275001 := by
  refine prime_of_cert 88599952463812275001 11 67 [2, 2, 2, 3, 5, 5, 5, 5, 5, 19, 281, 1187, 186406729] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_19
  · exact small_281
  · exact small_1187
  · exact prime_186406729

theorem prime_1647781915921980690468599 : Nat.Prime 1647781915921980690468599 := by
  refine prime_of_cert 1647781915921980690468599 13 81 [2, 17, 547, 88599952463812275001] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_17
  · exact small_547
  · exact prime_88599952463812275001

theorem prime_161969 : Nat.Prime 161969 := by
  refine prime_of_cert 161969 3 18 [2, 2, 2, 2, 53, 191] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_53
  · exact small_191

theorem prime_370471 : Nat.Prime 370471 := by
  refine prime_of_cert 370471 3 19 [2, 3, 5, 53, 233] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_53
  · exact small_233

theorem prime_133279 : Nat.Prime 133279 := by
  refine prime_of_cert 133279 3 18 [2, 3, 97, 229] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_97
  · exact small_229

theorem prime_65677 : Nat.Prime 65677 := by
  refine prime_of_cert 65677 2 17 [2, 2, 3, 13, 421] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_13
  · exact small_421

theorem prime_92581 : Nat.Prime 92581 := by
  refine prime_of_cert 92581 6 17 [2, 2, 3, 5, 1543] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_1543

theorem prime_10924559 : Nat.Prime 10924559 := by
  refine prime_of_cert 10924559 7 24 [2, 59, 92581] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_59
  · exact prime_92581

theorem prime_3473195323567808068309 : Nat.Prime 3473195323567808068309 := by
  refine prime_of_cert 3473195323567808068309 2 72 [2, 2, 3, 3, 13, 19, 59, 9227, 65677, 10924559] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_13
  · exact small_19
  · exact small_59
  · exact small_9227
  · exact prime_65677
  · exact prime_10924559

theorem prime_144471089338257942164514676806340723 : Nat.Prime 144471089338257942164514676806340723 := by
  refine prime_of_cert 144471089338257942164514676806340723 11 117 [2, 3, 3, 11, 109, 14461, 133279, 3473195323567808068309] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_11
  · exact small_109
  · exact small_14461
  · exact prime_133279
  · exact prime_3473195323567808068309

theorem prime_10577321 : Nat.Prime 10577321 := by
  refine prime_of_cert 10577321 17 24 [2, 2, 2, 5, 13, 20341] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_13
  · exact small_20341

theorem prime_495527 : Nat.Prime 495527 := by
  refine prime_of_cert 495527 5 19 [2, 41, 6043] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_41
  · exact small_6043

theorem prime_6937379 : Nat.Prime 6937379 := by
  refine prime_of_cert 6937379 2 23 [2, 7, 495527] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_7
  · exact prime_495527

theorem prime_101785224689 : Nat.Prime 101785224689 := by
  refine prime_of_cert 101785224689 3 37 [2, 2, 2, 2, 7, 131, 6937379] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_131
  · exact prime_6937379

theorem prime_8196883 : Nat.Prime 8196883 := by
  refine prime_of_cert 8196883 2 23 [2, 3, 79, 17293] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_79
  · exact small_17293

theorem prime_43800962361397 : Nat.Prime 43800962361397 := by
  refine prime_of_cert 43800962361397 6 46 [2, 2, 3, 41, 10861, 8196883] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_41
  · exact small_10861
  · exact prime_8196883

theorem prime_777241 : Nat.Prime 777241 := by
  refine prime_of_cert 777241 7 20 [2, 2, 2, 3, 3, 5, 17, 127] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_17
  · exact small_127

theorem prime_19353437 : Nat.Prime 19353437 := by
  refine prime_of_cert 19353437 2 25 [2, 2, 277, 17467] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_277
  · exact small_17467

theorem prime_60018716061994831 : Nat.Prime 60018716061994831 := by
  refine prime_of_cert 60018716061994831 7 56 [2, 3, 5, 7, 19, 777241, 19353437] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_7
  · exact small_19
  · exact prime_777241
  · exact prime_19353437

theorem prime_4239602065187190872179 : Nat.Prime 4239602065187190872179 := by
  refine prime_of_cert 4239602065187190872179 2 72 [2, 3, 61, 193, 60018716061994831] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_61
  · exact small_193
  · exact prime_60018716061994831

theorem prime_7427946019382605513260578233234962521 : Nat.Prime 7427946019382605513260578233234962521 := by
  refine prime_of_cert 7427946019382605513260578233234962521 3 123 [2, 2, 2, 5, 43800962361397, 4239602065187190872179] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact prime_43800962361397
  · exact prime_4239602065187190872179

theorem prime_15994076126984618329123851002118749004583184815459808099 : Nat.Prime 15994076126984618329123851002118749004583184815459808099 := by
  refine prime_of_cert 15994076126984618329123851002118749004583184815459808099 2 184 [2, 10577321, 101785224689, 7427946019382605513260578233234962521] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact prime_10577321
  · exact prime_101785224689
  · exact prime_7427946019382605513260578233234962521

theorem prime_3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511 : Nat.Prime 3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511 := by
  refine prime_of_cert 3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511 19 361 [2, 5, 19, 263, 5449, 15601, 370471, 144471089338257942164514676806340723, 15994076126984618329123851002118749004583184815459808099] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_19
  · exact small_263
  · exact small_5449
  · exact small_15601
  · exact prime_370471
  · exact prime_144471089338257942164514676806340723
  · exact prime_15994076126984618329123851002118749004583184815459808099

theorem prime_3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943 : Nat.Prime 3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943 := by
  refine prime_of_cert 3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943 3 391 [2, 3, 3, 11, 31, 161969, 3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_11
  · exact small_31
  · exact prime_161969
  · exact prime_3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511

theorem prime_6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449 : Nat.Prime 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449 := by
  refine prime_of_cert 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449 3 521 [2, 2, 2, 7, 11, 1283, 1458105463, 1647781915921980690468599, 3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_11
  · exact small_1283
  · exact prime_1458105463
  · exact prime_1647781915921980690468599
  · exact prime_3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943

theorem n_prime : Nat.Prime Spec.P521.n := by
  rw [show Spec.P521.n =
    6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449 by decide +kernel]
  exact prime_6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449

end VG.Proof.P521
