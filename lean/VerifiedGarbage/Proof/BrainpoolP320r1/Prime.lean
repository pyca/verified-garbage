module
-- separate module: the target proofs (inversion modulo `n` by divsteps) import `n_prime` without the algebra of `Curve.lean`, as brainpoolP384r1's do

import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Spec.BrainpoolP320r1
public import VerifiedGarbage.Proof.Framework.IsPrime

/-!
# The brainpoolP320r1 field prime is prime

Pratt certificates (`Proof/Framework/Pratt.lean`) for RFC 5639's `p` and
`q` (here `n`), one theorem per prime of each tree, from the factors of
`p - 1` and `n - 1`. Factors below `2^16` are prime by trial division
(`prime_small`). The group law needs only `p` prime (`Weierstrass.Good`);
the inversions modulo `n` by divsteps need `n` prime.
-/

@[expose] public section

namespace VG.Proof.BrainpoolP320r1

open VG.Proof.Pratt

theorem small_2 : IsPrime 2 := prime_small _ (by decide +kernel)
theorem small_11 : IsPrime 11 := prime_small _ (by decide +kernel)
theorem small_13 : IsPrime 13 := prime_small _ (by decide +kernel)
theorem small_59 : IsPrime 59 := prime_small _ (by decide +kernel)
theorem small_151 : IsPrime 151 := prime_small _ (by decide +kernel)
theorem small_163 : IsPrime 163 := prime_small _ (by decide +kernel)
theorem small_3 : IsPrime 3 := prime_small _ (by decide +kernel)
theorem small_23 : IsPrime 23 := prime_small _ (by decide +kernel)
theorem small_53 : IsPrime 53 := prime_small _ (by decide +kernel)
theorem small_3083 : IsPrime 3083 := prime_small _ (by decide +kernel)
theorem small_5 : IsPrime 5 := prime_small _ (by decide +kernel)
theorem small_113 : IsPrime 113 := prime_small _ (by decide +kernel)
theorem small_373 : IsPrime 373 := prime_small _ (by decide +kernel)
theorem small_1187 : IsPrime 1187 := prime_small _ (by decide +kernel)
theorem small_17 : IsPrime 17 := prime_small _ (by decide +kernel)
theorem small_24841 : IsPrime 24841 := prime_small _ (by decide +kernel)
theorem small_103 : IsPrime 103 := prime_small _ (by decide +kernel)
theorem small_3691 : IsPrime 3691 := prime_small _ (by decide +kernel)
theorem small_10513 : IsPrime 10513 := prime_small _ (by decide +kernel)
theorem small_3943 : IsPrime 3943 := prime_small _ (by decide +kernel)
theorem small_6947 : IsPrime 6947 := prime_small _ (by decide +kernel)
theorem small_37 : IsPrime 37 := prime_small _ (by decide +kernel)
theorem small_43 : IsPrime 43 := prime_small _ (by decide +kernel)
theorem small_1889 : IsPrime 1889 := prime_small _ (by decide +kernel)
theorem small_409 : IsPrime 409 := prime_small _ (by decide +kernel)
theorem small_6959 : IsPrime 6959 := prime_small _ (by decide +kernel)
theorem small_7 : IsPrime 7 := prime_small _ (by decide +kernel)
theorem small_31 : IsPrime 31 := prime_small _ (by decide +kernel)
theorem small_227 : IsPrime 227 := prime_small _ (by decide +kernel)
theorem small_577 : IsPrime 577 := prime_small _ (by decide +kernel)
theorem small_89 : IsPrime 89 := prime_small _ (by decide +kernel)
theorem small_317 : IsPrime 317 := prime_small _ (by decide +kernel)
theorem small_28661 : IsPrime 28661 := prime_small _ (by decide +kernel)
theorem small_47 : IsPrime 47 := prime_small _ (by decide +kernel)
theorem small_2239 : IsPrime 2239 := prime_small _ (by decide +kernel)
theorem small_97 : IsPrime 97 := prime_small _ (by decide +kernel)
theorem small_647 : IsPrime 647 := prime_small _ (by decide +kernel)
theorem small_21143 : IsPrime 21143 := prime_small _ (by decide +kernel)
theorem small_4603 : IsPrime 4603 := prime_small _ (by decide +kernel)
theorem small_2293 : IsPrime 2293 := prime_small _ (by decide +kernel)
theorem small_7457 : IsPrime 7457 := prime_small _ (by decide +kernel)
theorem small_2029 : IsPrime 2029 := prime_small _ (by decide +kernel)
theorem small_39251 : IsPrime 39251 := prime_small _ (by decide +kernel)
theorem small_107 : IsPrime 107 := prime_small _ (by decide +kernel)
theorem small_19 : IsPrime 19 := prime_small _ (by decide +kernel)
theorem small_2777 : IsPrime 2777 := prime_small _ (by decide +kernel)
theorem small_44029 : IsPrime 44029 := prime_small _ (by decide +kernel)

theorem prime_98453 : IsPrime 98453 := by
  refine prime_of_cert 98453 2 17 [2, 2, 151, 163] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_151
  · exact small_163

theorem prime_196907 : IsPrime 196907 := by
  refine prime_of_cert 196907 2 18 [2, 98453] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact small_2
  · exact prime_98453

theorem prime_885503 : IsPrime 885503 := by
  refine prime_of_cert 885503 5 20 [2, 373, 1187] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_373
  · exact small_1187

theorem prime_79695271 : IsPrime 79695271 := by
  refine prime_of_cert 79695271 12 27 [2, 3, 3, 5, 885503] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact prime_885503

theorem prime_6484007248561 : IsPrime 6484007248561 := by
  refine prime_of_cert 6484007248561 11 43 [2, 2, 2, 2, 3, 3, 5, 113, 79695271] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_113
  · exact prime_79695271

theorem prime_146208281456251399783 : IsPrime 146208281456251399783 := by
  refine prime_of_cert 146208281456251399783 6 67 [2, 3, 23, 53, 3083, 6484007248561] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_23
  · exact small_53
  · exact small_3083
  · exact prime_6484007248561

theorem prime_546677 : IsPrime 546677 := by
  refine prime_of_cert 546677 2 20 [2, 2, 13, 10513] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_13
  · exact small_10513

theorem prime_161422784561 : IsPrime 161422784561 := by
  refine prime_of_cert 161422784561 3 38 [2, 2, 2, 2, 5, 3691, 546677] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_3691
  · exact prime_546677

theorem prime_2905610122099 : IsPrime 2905610122099 := by
  refine prime_of_cert 2905610122099 2 42 [2, 3, 3, 161422784561] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact prime_161422784561

theorem prime_1197111370304789 : IsPrime 1197111370304789 := by
  refine prime_of_cert 1197111370304789 2 51 [2, 2, 103, 2905610122099] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_103
  · exact prime_2905610122099

theorem prime_14365336443657469 : IsPrime 14365336443657469 := by
  refine prime_of_cert 14365336443657469 2 54 [2, 2, 3, 1197111370304789] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact prime_1197111370304789

theorem prime_312561497 : IsPrime 312561497 := by
  refine prime_of_cert 312561497 3 29 [2, 2, 2, 13, 37, 43, 1889] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_13
  · exact small_37
  · exact small_43
  · exact small_1889

theorem prime_547948229735387969 : IsPrime 547948229735387969 := by
  refine prime_of_cert 547948229735387969 3 59 [2, 2, 2, 2, 2, 2, 3943, 6947, 312561497] (by decide) (by decide +kernel) ?_
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
  · exact small_3943
  · exact small_6947
  · exact prime_312561497

theorem prime_6747833 : IsPrime 6747833 := by
  refine prime_of_cert 6747833 12 23 [2, 2, 2, 7, 13, 13, 23, 31] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_13
  · exact small_13
  · exact small_23
  · exact small_31

theorem prime_301251701 : IsPrime 301251701 := by
  refine prime_of_cert 301251701 2 29 [2, 2, 5, 5, 23, 227, 577] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_23
  · exact small_227
  · exact small_577

theorem prime_115716149475651296730461 : IsPrime 115716149475651296730461 := by
  refine prime_of_cert 115716149475651296730461 2 77 [2, 2, 5, 409, 6959, 6747833, 301251701] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_409
  · exact small_6959
  · exact prime_6747833
  · exact prime_301251701

theorem prime_2307908307480288228542246803936276549862379769663891118114524423 : IsPrime 2307908307480288228542246803936276549862379769663891118114524423 := by
  refine prime_of_cert 2307908307480288228542246803936276549862379769663891118114524423 3 211 [2, 3, 17, 24841, 14365336443657469, 547948229735387969, 115716149475651296730461] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_17
  · exact small_24841
  · exact prime_14365336443657469
  · exact prime_547948229735387969
  · exact prime_115716149475651296730461

theorem prime_1763593322239166354161909842446019520889512772719515192772960415288640868802149818095501499903527 : IsPrime 1763593322239166354161909842446019520889512772719515192772960415288640868802149818095501499903527 := by
  refine prime_of_cert 1763593322239166354161909842446019520889512772719515192772960415288640868802149818095501499903527 5 320 [2, 11, 11, 11, 13, 13, 59, 196907, 146208281456251399783, 2307908307480288228542246803936276549862379769663891118114524423] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_11
  · exact small_11
  · exact small_11
  · exact small_13
  · exact small_13
  · exact small_59
  · exact prime_196907
  · exact prime_146208281456251399783
  · exact prime_2307908307480288228542246803936276549862379769663891118114524423

theorem p_prime : IsPrime Spec.BrainpoolP320r1.p := by
  rw [show Spec.BrainpoolP320r1.p = 1763593322239166354161909842446019520889512772719515192772960415288640868802149818095501499903527 by decide +kernel]
  exact prime_1763593322239166354161909842446019520889512772719515192772960415288640868802149818095501499903527

theorem prime_197033 : IsPrime 197033 := by
  refine prime_of_cert 197033 3 18 [2, 2, 2, 11, 2239] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_11
  · exact small_2239

theorem prime_10064069 : IsPrime 10064069 := by
  refine prime_of_cert 10064069 2 24 [2, 2, 7, 17, 21143] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_17
  · exact small_21143

theorem prime_101267 : IsPrime 101267 := by
  refine prime_of_cert 101267 2 17 [2, 11, 4603] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_11
  · exact small_4603

theorem prime_631906081 : IsPrime 631906081 := by
  refine prime_of_cert 631906081 19 30 [2, 2, 2, 2, 2, 3, 5, 13, 101267] (by decide) (by decide +kernel) ?_
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
  · exact prime_101267

theorem prime_352829224197635293617251 : IsPrime 352829224197635293617251 := by
  refine prime_of_cert 352829224197635293617251 2 79 [2, 5, 5, 5, 7, 7, 7, 647, 10064069, 631906081] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_7
  · exact small_7
  · exact small_7
  · exact small_647
  · exact prime_10064069
  · exact prime_631906081

theorem prime_4484624887 : IsPrime 4484624887 := by
  refine prime_of_cert 4484624887 5 33 [2, 3, 3, 3, 7, 37, 43, 7457] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_7
  · exact small_37
  · exact small_43
  · exact small_7457

theorem prime_174197 : IsPrime 174197 := by
  refine prime_of_cert 174197 2 18 [2, 2, 11, 37, 107] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_11
  · exact small_37
  · exact small_107

theorem prime_205122193411 : IsPrime 205122193411 := by
  refine prime_of_cert 205122193411 3 38 [2, 3, 5, 39251, 174197] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_39251
  · exact prime_174197

theorem prime_4161929304309191 : IsPrime 4161929304309191 := by
  refine prime_of_cert 4161929304309191 7 52 [2, 5, 2029, 205122193411] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_2029
  · exact prime_205122193411

theorem prime_1055261 : IsPrime 1055261 := by
  refine prime_of_cert 1055261 10 21 [2, 2, 5, 19, 2777] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_19
  · exact small_2777

theorem prime_2110523 : IsPrime 2110523 := by
  refine prime_of_cert 2110523 2 22 [2, 1055261] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact small_2
  · exact prime_1055261

theorem prime_1872641429 : IsPrime 1872641429 := by
  refine prime_of_cert 1872641429 2 31 [2, 2, 7, 7, 7, 31, 44029] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_7
  · exact small_7
  · exact small_31
  · exact small_44029

theorem prime_23713516839944203 : IsPrime 23713516839944203 := by
  refine prime_of_cert 23713516839944203 22 55 [2, 3, 2110523, 1872641429] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact prime_2110523
  · exact prime_1872641429

theorem prime_56834084706324953499635029374333218339957513609 : IsPrime 56834084706324953499635029374333218339957513609 := by
  refine prime_of_cert 56834084706324953499635029374333218339957513609 3 156 [2, 2, 2, 7, 2293, 4484624887, 4161929304309191, 23713516839944203] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_2293
  · exact prime_4484624887
  · exact prime_4161929304309191
  · exact prime_23713516839944203

theorem prime_23341373081361435103090946041083073851794115571864009670215941767494551877 : IsPrime 23341373081361435103090946041083073851794115571864009670215941767494551877 := by
  refine prime_of_cert 23341373081361435103090946041083073851794115571864009670215941767494551877 2 244 [2, 2, 3, 97, 352829224197635293617251, 56834084706324953499635029374333218339957513609] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_97
  · exact prime_352829224197635293617251
  · exact prime_56834084706324953499635029374333218339957513609

theorem prime_299589410500344960818634453344053290288849906371853185689121682914766027672438458623 : IsPrime 299589410500344960818634453344053290288849906371853185689121682914766027672438458623 := by
  refine prime_of_cert 299589410500344960818634453344053290288849906371853185689121682914766027672438458623 7 278 [2, 3, 3, 7, 11, 47, 197033, 23341373081361435103090946041083073851794115571864009670215941767494551877] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_7
  · exact small_11
  · exact small_47
  · exact prime_197033
  · exact prime_23341373081361435103090946041083073851794115571864009670215941767494551877

theorem prime_1763593322239166354161909842446019520889512772717686063760686124016784784845843468355685258203921 : IsPrime 1763593322239166354161909842446019520889512772717686063760686124016784784845843468355685258203921 := by
  refine prime_of_cert 1763593322239166354161909842446019520889512772717686063760686124016784784845843468355685258203921 6 320 [2, 2, 2, 2, 5, 7, 13, 89, 317, 28661, 299589410500344960818634453344053290288849906371853185689121682914766027672438458623] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_7
  · exact small_13
  · exact small_89
  · exact small_317
  · exact small_28661
  · exact prime_299589410500344960818634453344053290288849906371853185689121682914766027672438458623

theorem n_prime : IsPrime Spec.BrainpoolP320r1.n := by
  rw [show Spec.BrainpoolP320r1.n = 1763593322239166354161909842446019520889512772717686063760686124016784784845843468355685258203921 by decide +kernel]
  exact prime_1763593322239166354161909842446019520889512772717686063760686124016784784845843468355685258203921

end VG.Proof.BrainpoolP320r1
