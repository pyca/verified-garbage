import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Spec.Secp256k1

/-! # Primality of secp256k1’s field and group order

Pratt certificates, checked by the kernel with `prime_of_cert`. Each
factor below `2^16` is checked by trial division (`prime_small`).
-/

namespace VG.Proof.Secp256k1

open VG.Proof.Pratt

theorem small_2 : Nat.Prime 2 := prime_small _ (by decide +kernel)
theorem small_3 : Nat.Prime 3 := prime_small _ (by decide +kernel)
theorem small_5 : Nat.Prime 5 := prime_small _ (by decide +kernel)
theorem small_7 : Nat.Prime 7 := prime_small _ (by decide +kernel)
theorem small_11 : Nat.Prime 11 := prime_small _ (by decide +kernel)
theorem small_17 : Nat.Prime 17 := prime_small _ (by decide +kernel)
theorem small_19 : Nat.Prime 19 := prime_small _ (by decide +kernel)
theorem small_29 : Nat.Prime 29 := prime_small _ (by decide +kernel)
theorem small_31 : Nat.Prime 31 := prime_small _ (by decide +kernel)
theorem small_41 : Nat.Prime 41 := prime_small _ (by decide +kernel)
theorem small_53 : Nat.Prime 53 := prime_small _ (by decide +kernel)
theorem small_59 : Nat.Prime 59 := prime_small _ (by decide +kernel)
theorem small_97 : Nat.Prime 97 := prime_small _ (by decide +kernel)
theorem small_101 : Nat.Prime 101 := prime_small _ (by decide +kernel)
theorem small_109 : Nat.Prime 109 := prime_small _ (by decide +kernel)
theorem small_113 : Nat.Prime 113 := prime_small _ (by decide +kernel)
theorem small_149 : Nat.Prime 149 := prime_small _ (by decide +kernel)
theorem small_239 : Nat.Prime 239 := prime_small _ (by decide +kernel)
theorem small_293 : Nat.Prime 293 := prime_small _ (by decide +kernel)
theorem small_461 : Nat.Prime 461 := prime_small _ (by decide +kernel)
theorem small_631 : Nat.Prime 631 := prime_small _ (by decide +kernel)
theorem small_797 : Nat.Prime 797 := prime_small _ (by decide +kernel)
theorem small_971 : Nat.Prime 971 := prime_small _ (by decide +kernel)
theorem small_1373 : Nat.Prime 1373 := prime_small _ (by decide +kernel)
theorem small_1627 : Nat.Prime 1627 := prime_small _ (by decide +kernel)
theorem small_1871 : Nat.Prime 1871 := prime_small _ (by decide +kernel)
theorem small_2011 : Nat.Prime 2011 := prime_small _ (by decide +kernel)
theorem small_2621 : Nat.Prime 2621 := prime_small _ (by decide +kernel)
theorem small_2657 : Nat.Prime 2657 := prime_small _ (by decide +kernel)
theorem small_2731 : Nat.Prime 2731 := prime_small _ (by decide +kernel)
theorem small_2861 : Nat.Prime 2861 := prime_small _ (by decide +kernel)
theorem small_4051 : Nat.Prime 4051 := prime_small _ (by decide +kernel)
theorem small_4423 : Nat.Prime 4423 := prime_small _ (by decide +kernel)
theorem small_5323 : Nat.Prime 5323 := prime_small _ (by decide +kernel)
theorem small_7723 : Nat.Prime 7723 := prime_small _ (by decide +kernel)
theorem small_9349 : Nat.Prime 9349 := prime_small _ (by decide +kernel)
theorem small_13441 : Nat.Prime 13441 := prime_small _ (by decide +kernel)
theorem small_16699 : Nat.Prime 16699 := prime_small _ (by decide +kernel)
theorem small_20113 : Nat.Prime 20113 := prime_small _ (by decide +kernel)
theorem small_24809 : Nat.Prime 24809 := prime_small _ (by decide +kernel)
theorem small_28181 : Nat.Prime 28181 := prime_small _ (by decide +kernel)
theorem small_41201 : Nat.Prime 41201 := prime_small _ (by decide +kernel)
theorem prime_13331831 : Nat.Prime 13331831 := by
  refine prime_of_cert 13331831 13 24 [2, 5, 971, 1373] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_971
  · exact small_1373

theorem prime_173378833005251801 : Nat.Prime 173378833005251801 := by
  refine prime_of_cert 173378833005251801 6 58 [2, 2, 2, 5, 5, 2621, 24809, 13331831] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_2621
  · exact small_24809
  · exact prime_13331831

theorem prime_22149492674086928081353 : Nat.Prime 22149492674086928081353 := by
  refine prime_of_cert 22149492674086928081353 5 75 [2, 2, 2, 3, 5323, 173378833005251801] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5323
  · exact prime_173378833005251801

theorem prime_132896956044521568488119 : Nat.Prime 132896956044521568488119 := by
  refine prime_of_cert 132896956044521568488119 6 77 [2, 3, 22149492674086928081353] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact prime_22149492674086928081353

theorem prime_96557 : Nat.Prime 96557 := by
  refine prime_of_cert 96557 2 17 [2, 2, 101, 239] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_101
  · exact small_239

theorem prime_107590001 : Nat.Prime 107590001 := by
  refine prime_of_cert 107590001 3 27 [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_7
  · exact small_29
  · exact small_53

theorem prime_1206781 : Nat.Prime 1206781 := by
  refine prime_of_cert 1206781 10 21 [2, 2, 3, 5, 20113] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_20113

theorem prime_7240687 : Nat.Prime 7240687 := by
  refine prime_of_cert 7240687 3 23 [2, 3, 1206781] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact prime_1206781

theorem prime_255515944373312847190720520512484175977 : Nat.Prime 255515944373312847190720520512484175977 := by
  refine prime_of_cert 255515944373312847190720520512484175977 3 128 [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 96557, 41201, 107590001, 7240687] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_7
  · exact small_11
  · exact small_1627
  · exact small_2657
  · exact small_4423
  · exact prime_96557
  · exact small_41201
  · exact prime_107590001
  · exact prime_7240687

theorem prime_205115282021455665897114700593932402728804164701536103180137503955397371 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  refine prime_of_cert 205115282021455665897114700593932402728804164701536103180137503955397371 10 237 [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_29
  · exact small_29
  · exact small_31
  · exact small_7723
  · exact prime_132896956044521568488119
  · exact prime_255515944373312847190720520512484175977

theorem prime_115792089237316195423570985008687907853269984665640564039457584007908834671663 : Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  refine prime_of_cert 115792089237316195423570985008687907853269984665640564039457584007908834671663 3 256 [2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_7
  · exact small_13441
  · exact prime_205115282021455665897114700593932402728804164701536103180137503955397371

theorem prime_85831 : Nat.Prime 85831 := by
  refine prime_of_cert 85831 3 17 [2, 3, 5, 2861] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_2861

theorem prime_4681609 : Nat.Prime 4681609 := by
  refine prime_of_cert 4681609 23 23 [2, 2, 2, 3, 97, 2011] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_97
  · exact small_2011

theorem prime_107361793816595537 : Nat.Prime 107361793816595537 := by
  refine prime_of_cert 107361793816595537 3 57 [2, 2, 2, 2, 16699, 85831, 4681609] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_16699
  · exact prime_85831
  · exact prime_4681609

theorem prime_120233 : Nat.Prime 120233 := by
  refine prime_of_cert 120233 3 17 [2, 2, 2, 7, 19, 113] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_19
  · exact small_113

theorem prime_44706919 : Nat.Prime 44706919 := by
  refine prime_of_cert 44706919 6 26 [2, 3, 797, 9349] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_797
  · exact small_9349

theorem prime_174723607534414371449 : Nat.Prime 174723607534414371449 := by
  refine prime_of_cert 174723607534414371449 3 68 [2, 2, 2, 17, 59, 4051, 120233, 44706919] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_17
  · exact small_59
  · exact small_4051
  · exact prime_120233
  · exact prime_44706919

theorem prime_305873 : Nat.Prime 305873 := by
  refine prime_of_cert 305873 3 19 [2, 2, 2, 2, 7, 2731] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_2731

theorem prime_545358713 : Nat.Prime 545358713 := by
  refine prime_of_cert 545358713 5 30 [2, 2, 2, 41, 59, 28181] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_41
  · exact small_59
  · exact small_28181

theorem prime_1627771 : Nat.Prime 1627771 := by
  refine prime_of_cert 1627771 3 21 [2, 3, 5, 29, 1871] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_29
  · exact small_1871

theorem prime_297159362677 : Nat.Prime 297159362677 := by
  refine prime_of_cert 297159362677 2 39 [2, 2, 3, 3, 11, 461, 1627771] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_11
  · exact small_461
  · exact prime_1627771

theorem prime_29047611873442575647497758179 : Nat.Prime 29047611873442575647497758179 := by
  refine prime_of_cert 29047611873442575647497758179 2 95 [2, 293, 305873, 545358713, 297159362677] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_293
  · exact prime_305873
  · exact prime_545358713
  · exact prime_297159362677

theorem prime_341948486974166000522343609283189 : Nat.Prime 341948486974166000522343609283189 := by
  refine prime_of_cert 341948486974166000522343609283189 2 109 [2, 2, 3, 3, 3, 109, 29047611873442575647497758179] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_109
  · exact prime_29047611873442575647497758179

theorem prime_115792089237316195423570985008687907852837564279074904382605163141518161494337 : Nat.Prime 115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
  refine prime_of_cert 115792089237316195423570985008687907852837564279074904382605163141518161494337 7 256 [2, 2, 2, 2, 2, 2, 3, 149, 631, 107361793816595537, 174723607534414371449, 341948486974166000522343609283189] (by decide) (by decide +kernel) ?_
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
  · exact small_3
  · exact small_149
  · exact small_631
  · exact prime_107361793816595537
  · exact prime_174723607534414371449
  · exact prime_341948486974166000522343609283189

theorem p_prime : Nat.Prime Spec.Secp256k1.p := prime_115792089237316195423570985008687907853269984665640564039457584007908834671663

theorem n_prime : Nat.Prime Spec.Secp256k1.n := prime_115792089237316195423570985008687907852837564279074904382605163141518161494337

end VG.Proof.Secp256k1
