import VerifiedGarbage.Proof.P192.Prime

/-! # Primality of the P-192 subgroup order

Pratt certificates checked by the kernel, for scalar inversion.
-/

namespace VG.Proof.P192

open VG.Proof.Pratt

theorem prime_15716741 : Nat.Prime 15716741 := by
  refine prime_of_cert 15716741 2 24 [2, 2, 5, 13, 60449] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_46245989 : Nat.Prime 46245989 := by
  refine prime_of_cert 46245989 2 26 [2, 2, 1693, 6829] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)

theorem prime_7244839476697597 : Nat.Prime 7244839476697597 := by
  refine prime_of_cert 7244839476697597 2 53 [2, 2, 3, 239, 54623, 46245989] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_46245989

theorem prime_9564682313913860059195669 : Nat.Prime 9564682313913860059195669 := by
  refine prime_of_cert 9564682313913860059195669 2 83 [2, 2, 3, 7, 15716741, 7244839476697597] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_15716741
  · exact prime_7244839476697597

theorem prime_51920273 : Nat.Prime 51920273 := by
  refine prime_of_cert 51920273 3 26 [2, 2, 2, 2, 61, 53197] (by decide) (by decide +kernel) ?_
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

theorem prime_103840547 : Nat.Prime 103840547 := by
  refine prime_of_cert 103840547 2 27 [2, 51920273] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_51920273

theorem prime_7532705587894727 : Nat.Prime 7532705587894727 := by
  refine prime_of_cert 7532705587894727 5 53 [2, 29, 43, 43, 331, 4127, 51419] (by decide) (by decide +kernel) ?_
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

theorem prime_3433859179316188682119986911 : Nat.Prime 3433859179316188682119986911 := by
  refine prime_of_cert 3433859179316188682119986911 13 92 [2, 5, 439, 103840547, 7532705587894727] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_small _ (by decide +kernel)
  · exact prime_103840547
  · exact prime_7532705587894727

theorem prime_6277101735386680763835789423176059013767194773182842284081 : Nat.Prime 6277101735386680763835789423176059013767194773182842284081 := by
  refine prime_of_cert 6277101735386680763835789423176059013767194773182842284081 3 192 [2, 2, 2, 2, 5, 2389, 9564682313913860059195669, 3433859179316188682119986911] (by decide) (by decide +kernel) ?_
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
  · exact prime_9564682313913860059195669
  · exact prime_3433859179316188682119986911

theorem n_prime : Nat.Prime Spec.P192.n := prime_6277101735386680763835789423176059013767194773182842284081

end VG.Proof.P192
