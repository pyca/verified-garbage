import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Spec.P384

/-!
# The P-384 field prime `p` is prime

A Pratt certificate (`Proof/Framework/Pratt.lean`), one theorem per prime of
the tree. Factors below `2^16` are prime by trial division (`prime_small`).
The group law needs only `p` prime (`Weierstrass.Good`).
-/

namespace VG.Proof.P384

open VG.Proof.Pratt

theorem prime_2862218959 : Nat.Prime 2862218959 := by
  refine prime_of_cert 2862218959 3 32 [2, 3, 157, 1373, 2213] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_807145746439 : Nat.Prime 807145746439 := by
  refine prime_of_cert 807145746439 3 40 [2, 3, 47, 2862218959] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_2862218959

theorem prime_312289 : Nat.Prime 312289 := by
  refine prime_of_cert 312289 14 19 [2, 2, 2, 2, 2, 3, 3253] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_513928823 : Nat.Prime 513928823 := by
  refine prime_of_cert 513928823 5 29 [2, 11, 59, 599, 661] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_53448597593 : Nat.Prime 53448597593 := by
  refine prime_of_cert 53448597593 3 36 [2, 2, 2, 13, 513928823] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_513928823

theorem prime_1357291859799823621 : Nat.Prime 1357291859799823621 := by
  refine prime_of_cert 1357291859799823621 2 61 [2, 2, 3, 5, 67, 6317, 53448597593] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_53448597593

theorem prime_105957871 : Nat.Prime 105957871 := by
  refine prime_of_cert 105957871 3 27 [2, 3, 5, 19, 211, 881] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_246608641 : Nat.Prime 246608641 := by
  refine prime_of_cert 246608641 19 28 [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 21407] (by decide) (by decide +kernel) ?_
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

theorem prime_529709925838459440593 : Nat.Prime 529709925838459440593 := by
  refine prime_of_cert 529709925838459440593 3 69 [2, 2, 2, 2, 7, 181, 105957871, 246608641] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_105957871
  · exact prime_246608641

theorem prime_6051631 : Nat.Prime 6051631 := by
  refine prime_of_cert 6051631 6 23 [2, 3, 5, 13, 59, 263] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_336757 : Nat.Prime 336757 := by
  refine prime_of_cert 336757 2 19 [2, 2, 3, 7, 19, 211] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_568151 : Nat.Prime 568151 := by
  refine prime_of_cert 568151 17 20 [2, 5, 5, 11, 1033] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_363557 : Nat.Prime 363557 := by
  refine prime_of_cert 363557 2 19 [2, 2, 97, 937] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_532247449 : Nat.Prime 532247449 := by
  refine prime_of_cert 532247449 7 29 [2, 2, 2, 3, 61, 363557] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_363557

theorem prime_44925942675193 : Nat.Prime 44925942675193 := by
  refine prime_of_cert 44925942675193 5 46 [2, 2, 2, 3, 3517, 532247449] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_532247449

theorem prime_35581458644053887931343 : Nat.Prime 35581458644053887931343 := by
  refine prime_of_cert 35581458644053887931343 5 75 [2, 17, 41, 568151, 44925942675193] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_568151
  · exact prime_44925942675193

theorem prime_23964610537191310276190549303 : Nat.Prime 23964610537191310276190549303 := by
  refine prime_of_cert 23964610537191310276190549303 5 95 [2, 336757, 35581458644053887931343] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_336757
  · exact prime_35581458644053887931343

theorem prime_862725979338887169942859774909 : Nat.Prime 862725979338887169942859774909 := by
  refine prime_of_cert 862725979338887169942859774909 2 100 [2, 2, 3, 3, 23964610537191310276190549303] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_23964610537191310276190549303

theorem prime_20705423504133292078628634597817 : Nat.Prime 20705423504133292078628634597817 := by
  refine prime_of_cert 20705423504133292078628634597817 5 105 [2, 2, 2, 3, 862725979338887169942859774909] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_862725979338887169942859774909

theorem prime_413244619895455989650825325680172591660047 : Nat.Prime 413244619895455989650825325680172591660047 := by
  refine prime_of_cert 413244619895455989650825325680172591660047 5 139 [2, 17, 97, 6051631, 20705423504133292078628634597817] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_6051631
  · exact prime_20705423504133292078628634597817

theorem prime_12397338596863679689524759770405177749801411 : Nat.Prime 12397338596863679689524759770405177749801411 := by
  refine prime_of_cert 12397338596863679689524759770405177749801411 2 144 [2, 3, 5, 413244619895455989650825325680172591660047] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_413244619895455989650825325680172591660047

theorem prime_19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 : Nat.Prime 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 := by
  refine prime_of_cert 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 3 334 [2, 2, 2, 2, 11, 11, 11, 8389, 38557, 312289, 1357291859799823621, 529709925838459440593, 12397338596863679689524759770405177749801411] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
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
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_807145746439
  · exact prime_19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097

theorem p_prime : Nat.Prime Spec.P384.p := by
  rw [show Spec.P384.p =
    39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 by decide +kernel]
  exact prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

end VG.Proof.P384
