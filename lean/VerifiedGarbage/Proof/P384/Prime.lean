import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Spec.P384

/-!
# The P-384 field prime `p` and group order `n` are prime

Pratt certificates (`Proof/Framework/Pratt.lean`), one theorem per prime of
the trees; for `n`, from the factors of `n - 1` and recursively of each
`q - 1` (as factordb.com lists them; the certificates check them). Factors
below `2^16` are prime by trial division (`prime_small`). The group law
needs only `p` prime (`Weierstrass.Good`); the inversion modulo `n` by
divsteps needs `n` prime (`InvSound`).
-/

namespace VG.Proof.P384

open VG.Proof.Pratt

theorem small_2 : Nat.Prime 2 := prime_small _ (by decide +kernel)
theorem small_3 : Nat.Prime 3 := prime_small _ (by decide +kernel)
theorem small_5 : Nat.Prime 5 := prime_small _ (by decide +kernel)
theorem small_7 : Nat.Prime 7 := prime_small _ (by decide +kernel)
theorem small_11 : Nat.Prime 11 := prime_small _ (by decide +kernel)
theorem small_13 : Nat.Prime 13 := prime_small _ (by decide +kernel)
theorem small_17 : Nat.Prime 17 := prime_small _ (by decide +kernel)
theorem small_19 : Nat.Prime 19 := prime_small _ (by decide +kernel)
theorem small_29 : Nat.Prime 29 := prime_small _ (by decide +kernel)
theorem small_41 : Nat.Prime 41 := prime_small _ (by decide +kernel)
theorem small_47 : Nat.Prime 47 := prime_small _ (by decide +kernel)
theorem small_59 : Nat.Prime 59 := prime_small _ (by decide +kernel)
theorem small_61 : Nat.Prime 61 := prime_small _ (by decide +kernel)
theorem small_67 : Nat.Prime 67 := prime_small _ (by decide +kernel)
theorem small_73 : Nat.Prime 73 := prime_small _ (by decide +kernel)
theorem small_79 : Nat.Prime 79 := prime_small _ (by decide +kernel)
theorem small_89 : Nat.Prime 89 := prime_small _ (by decide +kernel)
theorem small_97 : Nat.Prime 97 := prime_small _ (by decide +kernel)
theorem small_107 : Nat.Prime 107 := prime_small _ (by decide +kernel)
theorem small_113 : Nat.Prime 113 := prime_small _ (by decide +kernel)
theorem small_149 : Nat.Prime 149 := prime_small _ (by decide +kernel)
theorem small_151 : Nat.Prime 151 := prime_small _ (by decide +kernel)
theorem small_157 : Nat.Prime 157 := prime_small _ (by decide +kernel)
theorem small_179 : Nat.Prime 179 := prime_small _ (by decide +kernel)
theorem small_181 : Nat.Prime 181 := prime_small _ (by decide +kernel)
theorem small_211 : Nat.Prime 211 := prime_small _ (by decide +kernel)
theorem small_233 : Nat.Prime 233 := prime_small _ (by decide +kernel)
theorem small_251 : Nat.Prime 251 := prime_small _ (by decide +kernel)
theorem small_263 : Nat.Prime 263 := prime_small _ (by decide +kernel)
theorem small_311 : Nat.Prime 311 := prime_small _ (by decide +kernel)
theorem small_347 : Nat.Prime 347 := prime_small _ (by decide +kernel)
theorem small_421 : Nat.Prime 421 := prime_small _ (by decide +kernel)
theorem small_491 : Nat.Prime 491 := prime_small _ (by decide +kernel)
theorem small_599 : Nat.Prime 599 := prime_small _ (by decide +kernel)
theorem small_659 : Nat.Prime 659 := prime_small _ (by decide +kernel)
theorem small_661 : Nat.Prime 661 := prime_small _ (by decide +kernel)
theorem small_881 : Nat.Prime 881 := prime_small _ (by decide +kernel)
theorem small_937 : Nat.Prime 937 := prime_small _ (by decide +kernel)
theorem small_1033 : Nat.Prime 1033 := prime_small _ (by decide +kernel)
theorem small_1117 : Nat.Prime 1117 := prime_small _ (by decide +kernel)
theorem small_1373 : Nat.Prime 1373 := prime_small _ (by decide +kernel)
theorem small_1553 : Nat.Prime 1553 := prime_small _ (by decide +kernel)
theorem small_2213 : Nat.Prime 2213 := prime_small _ (by decide +kernel)
theorem small_3253 : Nat.Prime 3253 := prime_small _ (by decide +kernel)
theorem small_3517 : Nat.Prime 3517 := prime_small _ (by decide +kernel)
theorem small_3739 : Nat.Prime 3739 := prime_small _ (by decide +kernel)
theorem small_6317 : Nat.Prime 6317 := prime_small _ (by decide +kernel)
theorem small_8389 : Nat.Prime 8389 := prime_small _ (by decide +kernel)
theorem small_8699 : Nat.Prime 8699 := prime_small _ (by decide +kernel)
theorem small_16979 : Nat.Prime 16979 := prime_small _ (by decide +kernel)
theorem small_21407 : Nat.Prime 21407 := prime_small _ (by decide +kernel)
theorem small_34429 : Nat.Prime 34429 := prime_small _ (by decide +kernel)
theorem small_37447 : Nat.Prime 37447 := prime_small _ (by decide +kernel)
theorem small_38557 : Nat.Prime 38557 := prime_small _ (by decide +kernel)
theorem small_64901 : Nat.Prime 64901 := prime_small _ (by decide +kernel)

theorem prime_2862218959 : Nat.Prime 2862218959 := by
  refine prime_of_cert 2862218959 3 32 [2, 3, 157, 1373, 2213] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_157
  · exact small_1373
  · exact small_2213

theorem prime_807145746439 : Nat.Prime 807145746439 := by
  refine prime_of_cert 807145746439 3 40 [2, 3, 47, 2862218959] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_47
  · exact prime_2862218959

theorem prime_312289 : Nat.Prime 312289 := by
  refine prime_of_cert 312289 14 19 [2, 2, 2, 2, 2, 3, 3253] (by decide) (by decide +kernel) ?_
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
  · exact small_3253

theorem prime_513928823 : Nat.Prime 513928823 := by
  refine prime_of_cert 513928823 5 29 [2, 11, 59, 599, 661] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_11
  · exact small_59
  · exact small_599
  · exact small_661

theorem prime_53448597593 : Nat.Prime 53448597593 := by
  refine prime_of_cert 53448597593 3 36 [2, 2, 2, 13, 513928823] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_13
  · exact prime_513928823

theorem prime_1357291859799823621 : Nat.Prime 1357291859799823621 := by
  refine prime_of_cert 1357291859799823621 2 61 [2, 2, 3, 5, 67, 6317, 53448597593] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_67
  · exact small_6317
  · exact prime_53448597593

theorem prime_105957871 : Nat.Prime 105957871 := by
  refine prime_of_cert 105957871 3 27 [2, 3, 5, 19, 211, 881] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_19
  · exact small_211
  · exact small_881

theorem prime_246608641 : Nat.Prime 246608641 := by
  refine prime_of_cert 246608641 19 28 [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 21407] (by decide) (by decide +kernel) ?_
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
  · exact small_5
  · exact small_21407

theorem prime_529709925838459440593 : Nat.Prime 529709925838459440593 := by
  refine prime_of_cert 529709925838459440593 3 69 [2, 2, 2, 2, 7, 181, 105957871, 246608641] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_181
  · exact prime_105957871
  · exact prime_246608641

theorem prime_6051631 : Nat.Prime 6051631 := by
  refine prime_of_cert 6051631 6 23 [2, 3, 5, 13, 59, 263] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_13
  · exact small_59
  · exact small_263

theorem prime_336757 : Nat.Prime 336757 := by
  refine prime_of_cert 336757 2 19 [2, 2, 3, 7, 19, 211] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_7
  · exact small_19
  · exact small_211

theorem prime_568151 : Nat.Prime 568151 := by
  refine prime_of_cert 568151 17 20 [2, 5, 5, 11, 1033] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_11
  · exact small_1033

theorem prime_363557 : Nat.Prime 363557 := by
  refine prime_of_cert 363557 2 19 [2, 2, 97, 937] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_97
  · exact small_937

theorem prime_532247449 : Nat.Prime 532247449 := by
  refine prime_of_cert 532247449 7 29 [2, 2, 2, 3, 61, 363557] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_61
  · exact prime_363557

theorem prime_44925942675193 : Nat.Prime 44925942675193 := by
  refine prime_of_cert 44925942675193 5 46 [2, 2, 2, 3, 3517, 532247449] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3517
  · exact prime_532247449

theorem prime_35581458644053887931343 : Nat.Prime 35581458644053887931343 := by
  refine prime_of_cert 35581458644053887931343 5 75 [2, 17, 41, 568151, 44925942675193] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_17
  · exact small_41
  · exact prime_568151
  · exact prime_44925942675193

theorem prime_23964610537191310276190549303 : Nat.Prime 23964610537191310276190549303 := by
  refine prime_of_cert 23964610537191310276190549303 5 95 [2, 336757, 35581458644053887931343] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact prime_336757
  · exact prime_35581458644053887931343

theorem prime_862725979338887169942859774909 : Nat.Prime 862725979338887169942859774909 := by
  refine prime_of_cert 862725979338887169942859774909 2 100 [2, 2, 3, 3, 23964610537191310276190549303] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact prime_23964610537191310276190549303

theorem prime_20705423504133292078628634597817 : Nat.Prime 20705423504133292078628634597817 := by
  refine prime_of_cert 20705423504133292078628634597817 5 105 [2, 2, 2, 3, 862725979338887169942859774909] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact prime_862725979338887169942859774909

theorem prime_413244619895455989650825325680172591660047 : Nat.Prime 413244619895455989650825325680172591660047 := by
  refine prime_of_cert 413244619895455989650825325680172591660047 5 139 [2, 17, 97, 6051631, 20705423504133292078628634597817] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_17
  · exact small_97
  · exact prime_6051631
  · exact prime_20705423504133292078628634597817

theorem prime_12397338596863679689524759770405177749801411 : Nat.Prime 12397338596863679689524759770405177749801411 := by
  refine prime_of_cert 12397338596863679689524759770405177749801411 2 144 [2, 3, 5, 413244619895455989650825325680172591660047] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact prime_413244619895455989650825325680172591660047

theorem prime_19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 : Nat.Prime 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 := by
  refine prime_of_cert 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 3 334 [2, 2, 2, 2, 11, 11, 11, 8389, 38557, 312289, 1357291859799823621, 529709925838459440593, 12397338596863679689524759770405177749801411] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_11
  · exact small_11
  · exact small_11
  · exact small_8389
  · exact small_38557
  · exact prime_312289
  · exact prime_1357291859799823621
  · exact prime_529709925838459440593
  · exact prime_12397338596863679689524759770405177749801411

theorem prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 : Nat.Prime 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 := by
  refine prime_of_cert 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 19 384 [2, 19, 67, 807145746439, 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_19
  · exact small_67
  · exact prime_807145746439
  · exact prime_19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097

theorem p_prime : Nat.Prime Spec.P384.p := by
  rw [show Spec.P384.p =
    39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 by decide +kernel]
  exact prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

theorem prime_290064143 : Nat.Prime 290064143 := by
  refine prime_of_cert 290064143 5 29 [2, 79, 491, 3739] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_79
  · exact small_491
  · exact small_3739

theorem prime_455737 : Nat.Prime 455737 := by
  refine prime_of_cert 455737 11 19 [2, 2, 2, 3, 17, 1117] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_17
  · exact small_1117

theorem prime_154950581 : Nat.Prime 154950581 := by
  refine prime_of_cert 154950581 2 28 [2, 2, 5, 17, 455737] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_17
  · exact prime_455737

theorem prime_120699720968197491947347 : Nat.Prime 120699720968197491947347 := by
  refine prime_of_cert 120699720968197491947347 3 77 [2, 3, 13, 34429, 154950581, 290064143] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_13
  · exact small_34429
  · exact prime_154950581
  · exact prime_290064143

theorem prime_1124679999981664229965379347 : Nat.Prime 1124679999981664229965379347 := by
  refine prime_of_cert 1124679999981664229965379347 2 90 [2, 3, 1553, 120699720968197491947347] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_1553
  · exact prime_120699720968197491947347

theorem prime_1276987 : Nat.Prime 1276987 := by
  refine prime_of_cert 1276987 2 21 [2, 3, 29, 41, 179] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_29
  · exact small_41
  · exact small_179

theorem prime_330563 : Nat.Prime 330563 := by
  refine prime_of_cert 330563 2 19 [2, 19, 8699] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_19
  · exact small_8699

theorem prime_1436833069313 : Nat.Prime 1436833069313 := by
  refine prime_of_cert 1436833069313 3 41 [2, 2, 2, 2, 2, 2, 2, 2, 16979, 330563] (by decide) (by decide +kernel) ?_
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
  · exact small_16979
  · exact prime_330563

theorem prime_248431 : Nat.Prime 248431 := by
  refine prime_of_cert 248431 3 18 [2, 3, 5, 7, 7, 13, 13] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_7
  · exact small_7
  · exact small_13
  · exact small_13

theorem prime_8463023 : Nat.Prime 8463023 := by
  refine prime_of_cert 8463023 5 24 [2, 113, 37447] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_113
  · exact small_37447

theorem prime_9863677 : Nat.Prime 9863677 := by
  refine prime_of_cert 9863677 5 24 [2, 2, 3, 3, 311, 881] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_311
  · exact small_881

theorem prime_37344768852931 : Nat.Prime 37344768852931 := by
  refine prime_of_cert 37344768852931 3 46 [2, 3, 5, 7, 11, 11, 149, 9863677] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_7
  · exact small_11
  · exact small_11
  · exact small_149
  · exact prime_9863677

theorem prime_55942463741690639 : Nat.Prime 55942463741690639 := by
  refine prime_of_cert 55942463741690639 7 56 [2, 7, 107, 37344768852931] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_7
  · exact small_107
  · exact prime_37344768852931

theorem prime_272109983 : Nat.Prime 272109983 := by
  refine prime_of_cert 272109983 5 29 [2, 19, 73, 233, 421] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_19
  · exact small_73
  · exact small_233
  · exact small_421

theorem prime_228572385721 : Nat.Prime 228572385721 := by
  refine prime_of_cert 228572385721 23 38 [2, 2, 2, 3, 5, 7, 272109983] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_7
  · exact prime_272109983

theorem prime_23314383343543 : Nat.Prime 23314383343543 := by
  refine prime_of_cert 23314383343543 3 45 [2, 3, 17, 228572385721] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_17
  · exact prime_228572385721

theorem prime_426632512014427833817 : Nat.Prime 426632512014427833817 := by
  refine prime_of_cert 426632512014427833817 11 69 [2, 2, 2, 3, 13, 89, 659, 23314383343543] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_13
  · exact small_89
  · exact small_659
  · exact prime_23314383343543

theorem prime_1495199339761412565498084319 : Nat.Prime 1495199339761412565498084319 := by
  refine prime_of_cert 1495199339761412565498084319 6 91 [2, 3, 3, 3, 64901, 426632512014427833817] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_64901
  · exact prime_426632512014427833817

theorem prime_17942392077136950785977011829 : Nat.Prime 17942392077136950785977011829 := by
  refine prime_of_cert 17942392077136950785977011829 6 94 [2, 2, 3, 1495199339761412565498084319] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact prime_1495199339761412565498084319

theorem prime_1059392654943455286185473617842338478315215895509773412096307 : Nat.Prime 1059392654943455286185473617842338478315215895509773412096307 := by
  refine prime_of_cert 1059392654943455286185473617842338478315215895509773412096307 2 200 [2, 251, 248431, 8463023, 55942463741690639, 17942392077136950785977011829] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_251
  · exact prime_248431
  · exact prime_8463023
  · exact prime_55942463741690639
  · exact prime_17942392077136950785977011829

theorem prime_3055465788140352002733946906144561090641249606160407884365391979704929268480326390471 : Nat.Prime 3055465788140352002733946906144561090641249606160407884365391979704929268480326390471 := by
  refine prime_of_cert 3055465788140352002733946906144561090641249606160407884365391979704929268480326390471 12 281 [2, 3, 5, 151, 347, 1276987, 1436833069313, 1059392654943455286185473617842338478315215895509773412096307] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_151
  · exact small_347
  · exact prime_1276987
  · exact prime_1436833069313
  · exact prime_1059392654943455286185473617842338478315215895509773412096307

theorem prime_39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643 : Nat.Prime 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643 := by
  refine prime_of_cert 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643 2 384 [2, 3, 3, 7, 7, 13, 1124679999981664229965379347, 3055465788140352002733946906144561090641249606160407884365391979704929268480326390471] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_7
  · exact small_7
  · exact small_13
  · exact prime_1124679999981664229965379347
  · exact prime_3055465788140352002733946906144561090641249606160407884365391979704929268480326390471

theorem n_prime : Nat.Prime Spec.P384.n := by
  rw [show Spec.P384.n =
    39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643 by decide +kernel]
  exact prime_39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643

end VG.Proof.P384
