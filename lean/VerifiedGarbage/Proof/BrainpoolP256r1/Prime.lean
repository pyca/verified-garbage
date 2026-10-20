module

import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Spec.BrainpoolP256r1
public import Mathlib.Data.Nat.Prime.Defs

/-!
# The brainpoolP256r1 field prime is prime

Pratt certificates (`Proof/Framework/Pratt.lean`) for RFC 5639's `p` and
`q` (here `n`), one theorem per prime of each tree, from the factors of
`p - 1` and `n - 1`. Factors below `2^16` are prime by trial division
(`prime_small`). The group law needs only `p` prime (`Weierstrass.Good`);
the inversions modulo `n` by divsteps need `n` prime.
-/

@[expose] public section

namespace VG.Proof.BrainpoolP256r1

open VG.Proof.Pratt

theorem small_2 : Nat.Prime 2 := prime_small _ (by decide +kernel)
theorem small_3 : Nat.Prime 3 := prime_small _ (by decide +kernel)
theorem small_5 : Nat.Prime 5 := prime_small _ (by decide +kernel)
theorem small_7 : Nat.Prime 7 := prime_small _ (by decide +kernel)
theorem small_11 : Nat.Prime 11 := prime_small _ (by decide +kernel)
theorem small_13 : Nat.Prime 13 := prime_small _ (by decide +kernel)
theorem small_23 : Nat.Prime 23 := prime_small _ (by decide +kernel)
theorem small_29 : Nat.Prime 29 := prime_small _ (by decide +kernel)
theorem small_31 : Nat.Prime 31 := prime_small _ (by decide +kernel)
theorem small_53 : Nat.Prime 53 := prime_small _ (by decide +kernel)
theorem small_61 : Nat.Prime 61 := prime_small _ (by decide +kernel)
theorem small_73 : Nat.Prime 73 := prime_small _ (by decide +kernel)
theorem small_607 : Nat.Prime 607 := prime_small _ (by decide +kernel)
theorem small_829 : Nat.Prime 829 := prime_small _ (by decide +kernel)
theorem small_887 : Nat.Prime 887 := prime_small _ (by decide +kernel)
theorem small_929 : Nat.Prime 929 := prime_small _ (by decide +kernel)
theorem small_1259 : Nat.Prime 1259 := prime_small _ (by decide +kernel)
theorem small_1609 : Nat.Prime 1609 := prime_small _ (by decide +kernel)
theorem small_1667 : Nat.Prime 1667 := prime_small _ (by decide +kernel)
theorem small_2851 : Nat.Prime 2851 := prime_small _ (by decide +kernel)
theorem small_8039 : Nat.Prime 8039 := prime_small _ (by decide +kernel)
theorem small_9341 : Nat.Prime 9341 := prime_small _ (by decide +kernel)
theorem small_13309 : Nat.Prime 13309 := prime_small _ (by decide +kernel)
theorem small_22709 : Nat.Prime 22709 := prime_small _ (by decide +kernel)
theorem small_32533 : Nat.Prime 32533 := prime_small _ (by decide +kernel)
theorem small_17 : Nat.Prime 17 := prime_small _ (by decide +kernel)
theorem small_19 : Nat.Prime 19 := prime_small _ (by decide +kernel)
theorem small_41 : Nat.Prime 41 := prime_small _ (by decide +kernel)
theorem small_43 : Nat.Prime 43 := prime_small _ (by decide +kernel)
theorem small_139 : Nat.Prime 139 := prime_small _ (by decide +kernel)
theorem small_199 : Nat.Prime 199 := prime_small _ (by decide +kernel)
theorem small_223 : Nat.Prime 223 := prime_small _ (by decide +kernel)
theorem small_281 : Nat.Prime 281 := prime_small _ (by decide +kernel)
theorem small_521 : Nat.Prime 521 := prime_small _ (by decide +kernel)
theorem small_1543 : Nat.Prime 1543 := prime_small _ (by decide +kernel)
theorem small_1571 : Nat.Prime 1571 := prime_small _ (by decide +kernel)
theorem small_1783 : Nat.Prime 1783 := prime_small _ (by decide +kernel)
theorem small_9311 : Nat.Prime 9311 := prime_small _ (by decide +kernel)
theorem small_12281 : Nat.Prime 12281 := prime_small _ (by decide +kernel)
theorem small_21107 : Nat.Prime 21107 := prime_small _ (by decide +kernel)
theorem small_25951 : Nat.Prime 25951 := prime_small _ (by decide +kernel)
theorem small_50123 : Nat.Prime 50123 := prime_small _ (by decide +kernel)
theorem small_50993 : Nat.Prime 50993 := prime_small _ (by decide +kernel)
theorem small_55799 : Nat.Prime 55799 := prime_small _ (by decide +kernel)

theorem prime_74729 : Nat.Prime 74729 := by
  refine prime_of_cert 74729 3 17 [2, 2, 2, 9341] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_9341

theorem prime_149459 : Nat.Prime 149459 := by
  refine prime_of_cert 149459 2 18 [2, 74729] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact small_2
  · exact prime_74729

theorem prime_17543087 : Nat.Prime 17543087 := by
  refine prime_of_cert 17543087 5 25 [2, 11, 29, 31, 887] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_11
  · exact small_29
  · exact small_31
  · exact small_887

theorem prime_858397 : Nat.Prime 858397 := by
  refine prime_of_cert 858397 6 20 [2, 2, 3, 7, 11, 929] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_7
  · exact small_11
  · exact small_929

theorem prime_25659209 : Nat.Prime 25659209 := by
  refine prime_of_cert 25659209 3 25 [2, 2, 2, 53, 73, 829] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_53
  · exact small_73
  · exact small_829

theorem prime_1139592334882447158893 : Nat.Prime 1139592334882447158893 := by
  refine prime_of_cert 1139592334882447158893 2 70 [2, 2, 1609, 8039, 858397, 25659209] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_1609
  · exact small_8039
  · exact prime_858397
  · exact prime_25659209

theorem prime_10434257 : Nat.Prime 10434257 := by
  refine prime_of_cert 10434257 3 24 [2, 2, 2, 2, 7, 7, 13309] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_7
  · exact small_7
  · exact small_13309

theorem prime_187816627 : Nat.Prime 187816627 := by
  refine prime_of_cert 187816627 2 28 [2, 3, 3, 10434257] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact prime_10434257

theorem prime_151499460061 : Nat.Prime 151499460061 := by
  refine prime_of_cert 151499460061 2 38 [2, 2, 3, 3, 5, 13, 2851, 22709] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_13
  · exact small_2851
  · exact small_22709

theorem prime_921589 : Nat.Prime 921589 := by
  refine prime_of_cert 921589 2 20 [2, 2, 3, 61, 1259] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_61
  · exact small_1259

theorem prime_3686357 : Nat.Prime 3686357 := by
  refine prime_of_cert 3686357 2 22 [2, 2, 921589] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact prime_921589

theorem prime_719569513687 : Nat.Prime 719569513687 := by
  refine prime_of_cert 719569513687 3 40 [2, 3, 32533, 3686357] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_32533
  · exact prime_3686357

theorem prime_49712609355733181957277501974736893 : Nat.Prime 49712609355733181957277501974736893 := by
  refine prime_of_cert 49712609355733181957277501974736893 2 116 [2, 2, 607, 187816627, 151499460061, 719569513687] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_607
  · exact prime_187816627
  · exact prime_151499460061
  · exact prime_719569513687

theorem prime_3059213862715144055733503214373292934438943635608167530247 : Nat.Prime 3059213862715144055733503214373292934438943635608167530247 := by
  refine prime_of_cert 3059213862715144055733503214373292934438943635608167530247 5 191 [2, 3, 3, 3, 1139592334882447158893, 49712609355733181957277501974736893] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact prime_1139592334882447158893
  · exact prime_49712609355733181957277501974736893

theorem prime_76884956397045344220809746629001649093037950200943055203735601445031516197751 : Nat.Prime 76884956397045344220809746629001649093037950200943055203735601445031516197751 := by
  refine prime_of_cert 76884956397045344220809746629001649093037950200943055203735601445031516197751 11 256 [2, 5, 5, 5, 23, 1667, 149459, 17543087, 3059213862715144055733503214373292934438943635608167530247] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_23
  · exact small_1667
  · exact prime_149459
  · exact prime_17543087
  · exact prime_3059213862715144055733503214373292934438943635608167530247

theorem p_prime : Nat.Prime Spec.BrainpoolP256r1.p := by
  rw [show Spec.BrainpoolP256r1.p = 76884956397045344220809746629001649093037950200943055203735601445031516197751 by decide +kernel]
  exact prime_76884956397045344220809746629001649093037950200943055203735601445031516197751

theorem prime_84032791 : Nat.Prime 84032791 := by
  refine prime_of_cert 84032791 3 27 [2, 3, 5, 1571, 1783] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_1571
  · exact small_1783

theorem prime_68632771 : Nat.Prime 68632771 := by
  refine prime_of_cert 68632771 3 27 [2, 3, 5, 41, 55799] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_41
  · exact small_55799

theorem prime_7675751843099 : Nat.Prime 7675751843099 := by
  refine prime_of_cert 7675751843099 2 43 [2, 199, 281, 68632771] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_199
  · exact small_281
  · exact prime_68632771

theorem prime_245621 : Nat.Prime 245621 := by
  refine prime_of_cert 245621 2 18 [2, 2, 5, 12281] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_12281

theorem prime_757986407 : Nat.Prime 757986407 := by
  refine prime_of_cert 757986407 5 30 [2, 1543, 245621] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_1543
  · exact prime_245621

theorem prime_57660685428664091 : Nat.Prime 57660685428664091 := by
  refine prime_of_cert 57660685428664091 6 56 [2, 5, 19, 43, 9311, 757986407] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_19
  · exact small_43
  · exact small_9311
  · exact prime_757986407

theorem prime_41802583 : Nat.Prime 41802583 := by
  refine prime_of_cert 41802583 3 26 [2, 3, 139, 50123] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_139
  · exact small_50123

theorem prime_1674656872585139 : Nat.Prime 1674656872585139 := by
  refine prime_of_cert 1674656872585139 2 51 [2, 13, 73, 21107, 41802583] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_13
  · exact small_73
  · exact small_21107
  · exact prime_41802583

theorem prime_190455129210693390224369129 : Nat.Prime 190455129210693390224369129 := by
  refine prime_of_cert 190455129210693390224369129 3 88 [2, 2, 2, 17, 23, 23, 31, 50993, 1674656872585139] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_17
  · exact small_23
  · exact small_23
  · exact small_31
  · exact small_50993
  · exact prime_1674656872585139

theorem prime_114430077720284863765762092766225391679591020381 : Nat.Prime 114430077720284863765762092766225391679591020381 := by
  refine prime_of_cert 114430077720284863765762092766225391679591020381 2 157 [2, 2, 5, 521, 57660685428664091, 190455129210693390224369129] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_521
  · exact prime_57660685428664091
  · exact prime_190455129210693390224369129

theorem prime_4271386466502519123378319257166758282929862876911918307708639947947974242171 : Nat.Prime 4271386466502519123378319257166758282929862876911918307708639947947974242171 := by
  refine prime_of_cert 4271386466502519123378319257166758282929862876911918307708639947947974242171 2 252 [2, 5, 223, 25951, 84032791, 7675751843099, 114430077720284863765762092766225391679591020381] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_223
  · exact small_25951
  · exact prime_84032791
  · exact prime_7675751843099
  · exact prime_114430077720284863765762092766225391679591020381

theorem prime_76884956397045344220809746629001649092737531784414529538755519063063536359079 : Nat.Prime 76884956397045344220809746629001649092737531784414529538755519063063536359079 := by
  refine prime_of_cert 76884956397045344220809746629001649092737531784414529538755519063063536359079 3 256 [2, 3, 3, 4271386466502519123378319257166758282929862876911918307708639947947974242171] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact prime_4271386466502519123378319257166758282929862876911918307708639947947974242171

theorem n_prime : Nat.Prime Spec.BrainpoolP256r1.n := by
  rw [show Spec.BrainpoolP256r1.n = 76884956397045344220809746629001649092737531784414529538755519063063536359079 by decide +kernel]
  exact prime_76884956397045344220809746629001649092737531784414529538755519063063536359079

end VG.Proof.BrainpoolP256r1
