import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Spec.BrainpoolP384r1

/-!
# The brainpoolP384r1 field prime is prime

A Pratt certificate (`Proof/Framework/Pratt.lean`) for RFC 5639's `p`, one
theorem per prime of the tree, from the factors of `p - 1`. Factors below
`2^16` are prime by trial division (`prime_small`). The group law needs only
`p` prime (`Weierstrass.Good`).
-/

namespace VG.Proof.BrainpoolP384r1

open VG.Proof.Pratt

theorem prime_734647 : Nat.Prime 734647 := by
  refine prime_of_cert 734647 3 20 [2, 3, 11, 11131] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_78713 : Nat.Prime 78713 := by
  refine prime_of_cert 78713 3 17 [2, 2, 2, 9839] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_157427 : Nat.Prime 157427 := by
  refine prime_of_cert 157427 2 18 [2, 78713] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_78713

theorem prime_27093605140967 : Nat.Prime 27093605140967 := by
  refine prime_of_cert 27093605140967 5 45 [2, 7, 13, 83, 11393, 157427] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_157427

theorem prime_97151 : Nat.Prime 97151 := by
  refine prime_of_cert 97151 13 17 [2, 5, 5, 29, 67] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_59016512273 : Nat.Prime 59016512273 := by
  refine prime_of_cert 59016512273 3 36 [2, 2, 2, 2, 37967, 97151] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_97151

theorem prime_3012146720727260651 : Nat.Prime 3012146720727260651 := by
  refine prime_of_cert 3012146720727260651 13 62 [2, 5, 5, 283, 3607, 59016512273] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_59016512273

theorem prime_868583 : Nat.Prime 868583 := by
  refine prime_of_cert 868583 5 20 [2, 11, 13, 3037] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_1898722439 : Nat.Prime 1898722439 := by
  refine prime_of_cert 1898722439 11 31 [2, 1093, 868583] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_868583

theorem prime_123606883 : Nat.Prime 123606883 := by
  refine prime_of_cert 123606883 2 27 [2, 3, 3, 7, 41, 71, 337] (by decide) (by decide +kernel) ?_
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

theorem prime_13843970897 : Nat.Prime 13843970897 := by
  refine prime_of_cert 13843970897 5 34 [2, 2, 2, 2, 7, 123606883] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_123606883

theorem prime_8076987940436711 : Nat.Prime 8076987940436711 := by
  refine prime_of_cert 8076987940436711 7 53 [2, 5, 41, 1423, 13843970897] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_13843970897

theorem prime_726928914639303991 : Nat.Prime 726928914639303991 := by
  refine prime_of_cert 726928914639303991 3 60 [2, 3, 3, 5, 8076987940436711] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_8076987940436711

theorem prime_12811352796235023217778801482819 : Nat.Prime 12811352796235023217778801482819 := by
  refine prime_of_cert 12811352796235023217778801482819 2 104 [2, 3, 7, 13, 17, 1898722439, 726928914639303991] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_1898722439
  · exact prime_726928914639303991

theorem prime_991057 : Nat.Prime 991057 := by
  refine prime_of_cert 991057 10 20 [2, 2, 2, 2, 3, 11, 1877] (by decide) (by decide +kernel) ?_
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

theorem prime_95959 : Nat.Prime 95959 := by
  refine prime_of_cert 95959 3 17 [2, 3, 3, 3, 1777] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_2663886769 : Nat.Prime 2663886769 := by
  refine prime_of_cert 2663886769 7 32 [2, 2, 2, 2, 3, 41, 67, 89, 227] (by decide) (by decide +kernel) ?_
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

theorem prime_7057776167979264311 : Nat.Prime 7057776167979264311 := by
  refine prime_of_cert 7057776167979264311 11 63 [2, 5, 11, 251, 95959, 2663886769] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_95959
  · exact prime_2663886769

theorem prime_9511259360250244436150360929400467 : Nat.Prime 9511259360250244436150360929400467 := by
  refine prime_of_cert 9511259360250244436150360929400467 2 113 [2, 3, 3, 3, 3, 11, 73, 10453, 991057, 7057776167979264311] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_991057
  · exact prime_7057776167979264311

theorem prime_13857381403312519376221497559214358876512960238914501360589056738895920081 : Nat.Prime 13857381403312519376221497559214358876512960238914501360589056738895920081 := by
  refine prime_of_cert 13857381403312519376221497559214358876512960238914501360589056738895920081 3 243 [2, 2, 2, 2, 5, 13, 43, 2543, 12811352796235023217778801482819, 9511259360250244436150360929400467] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_12811352796235023217778801482819
  · exact prime_9511259360250244436150360929400467

theorem prime_21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 : Nat.Prime 21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 := by
  refine prime_of_cert 21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 3 384 [2, 3, 5, 11, 79, 734647, 27093605140967, 3012146720727260651, 13857381403312519376221497559214358876512960238914501360589056738895920081] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_734647
  · exact prime_27093605140967
  · exact prime_3012146720727260651
  · exact prime_13857381403312519376221497559214358876512960238914501360589056738895920081

theorem p_prime : Nat.Prime Spec.BrainpoolP384r1.p := by
  rw [show Spec.BrainpoolP384r1.p = 21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 by decide +kernel]
  exact prime_21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331

end VG.Proof.BrainpoolP384r1
