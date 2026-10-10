import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Spec.BrainpoolP512r1

/-!
# The brainpoolP512r1 field prime is prime

A Pratt certificate (`Proof/Framework/Pratt.lean`) for RFC 5639's `p`, one
theorem per prime of the tree, from the factors of `p - 1`. Factors below
`2^16` are prime by trial division (`prime_small`). The group law needs only
`p` prime (`Weierstrass.Good`).
-/

namespace VG.Proof.BrainpoolP512r1

open VG.Proof.Pratt

/-- The factors below `2^16`, each checked once. -/
theorem small_2 : Nat.Prime 2 := prime_small _ (by decide +kernel)
theorem small_3 : Nat.Prime 3 := prime_small _ (by decide +kernel)
theorem small_5 : Nat.Prime 5 := prime_small _ (by decide +kernel)
theorem small_7 : Nat.Prime 7 := prime_small _ (by decide +kernel)
theorem small_11 : Nat.Prime 11 := prime_small _ (by decide +kernel)
theorem small_13 : Nat.Prime 13 := prime_small _ (by decide +kernel)
theorem small_17 : Nat.Prime 17 := prime_small _ (by decide +kernel)
theorem small_19 : Nat.Prime 19 := prime_small _ (by decide +kernel)
theorem small_23 : Nat.Prime 23 := prime_small _ (by decide +kernel)
theorem small_29 : Nat.Prime 29 := prime_small _ (by decide +kernel)
theorem small_41 : Nat.Prime 41 := prime_small _ (by decide +kernel)
theorem small_47 : Nat.Prime 47 := prime_small _ (by decide +kernel)
theorem small_61 : Nat.Prime 61 := prime_small _ (by decide +kernel)
theorem small_71 : Nat.Prime 71 := prime_small _ (by decide +kernel)
theorem small_89 : Nat.Prime 89 := prime_small _ (by decide +kernel)
theorem small_101 : Nat.Prime 101 := prime_small _ (by decide +kernel)
theorem small_109 : Nat.Prime 109 := prime_small _ (by decide +kernel)
theorem small_127 : Nat.Prime 127 := prime_small _ (by decide +kernel)
theorem small_131 : Nat.Prime 131 := prime_small _ (by decide +kernel)
theorem small_149 : Nat.Prime 149 := prime_small _ (by decide +kernel)
theorem small_239 : Nat.Prime 239 := prime_small _ (by decide +kernel)
theorem small_277 : Nat.Prime 277 := prime_small _ (by decide +kernel)
theorem small_293 : Nat.Prime 293 := prime_small _ (by decide +kernel)
theorem small_1229 : Nat.Prime 1229 := prime_small _ (by decide +kernel)
theorem small_1601 : Nat.Prime 1601 := prime_small _ (by decide +kernel)
theorem small_1913 : Nat.Prime 1913 := prime_small _ (by decide +kernel)
theorem small_3347 : Nat.Prime 3347 := prime_small _ (by decide +kernel)
theorem small_3571 : Nat.Prime 3571 := prime_small _ (by decide +kernel)
theorem small_4021 : Nat.Prime 4021 := prime_small _ (by decide +kernel)
theorem small_4673 : Nat.Prime 4673 := prime_small _ (by decide +kernel)
theorem small_5717 : Nat.Prime 5717 := prime_small _ (by decide +kernel)
theorem small_15511 : Nat.Prime 15511 := prime_small _ (by decide +kernel)
theorem small_18211 : Nat.Prime 18211 := prime_small _ (by decide +kernel)
theorem small_19009 : Nat.Prime 19009 := prime_small _ (by decide +kernel)
theorem small_24379 : Nat.Prime 24379 := prime_small _ (by decide +kernel)
theorem small_28057 : Nat.Prime 28057 := prime_small _ (by decide +kernel)
theorem small_36587 : Nat.Prime 36587 := prime_small _ (by decide +kernel)
theorem small_37657 : Nat.Prime 37657 := prime_small _ (by decide +kernel)
theorem small_41539 : Nat.Prime 41539 := prime_small _ (by decide +kernel)

theorem prime_65797030259 : Nat.Prime 65797030259 := by
  refine prime_of_cert 65797030259 2 36 [2, 23, 47, 1601, 19009] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_23
  · exact small_47
  · exact small_1601
  · exact small_19009

theorem prime_60401673777763 : Nat.Prime 60401673777763 := by
  refine prime_of_cert 60401673777763 2 46 [2, 3, 3, 3, 17, 65797030259] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_17
  · exact prime_65797030259

theorem prime_329430728783919403 : Nat.Prime 329430728783919403 := by
  refine prime_of_cert 329430728783919403 2 59 [2, 3, 3, 3, 101, 60401673777763] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_101
  · exact prime_60401673777763

theorem prime_35143541 : Nat.Prime 35143541 := by
  refine prime_of_cert 35143541 2 26 [2, 2, 5, 19, 23, 4021] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_19
  · exact small_23
  · exact small_4021

theorem prime_1501501 : Nat.Prime 1501501 := by
  refine prime_of_cert 1501501 2 21 [2, 2, 3, 5, 5, 5, 7, 11, 13] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_7
  · exact small_11
  · exact small_13

theorem prime_54054037 : Nat.Prime 54054037 := by
  refine prime_of_cert 54054037 2 26 [2, 2, 3, 3, 1501501] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact prime_1501501

theorem prime_72186710089950647 : Nat.Prime 72186710089950647 := by
  refine prime_of_cert 72186710089950647 5 57 [2, 19, 35143541, 54054037] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_19
  · exact prime_35143541
  · exact prime_54054037

theorem prime_18335424362847464339 : Nat.Prime 18335424362847464339 := by
  refine prime_of_cert 18335424362847464339 2 64 [2, 127, 72186710089950647] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_127
  · exact prime_72186710089950647

theorem prime_8360987 : Nat.Prime 8360987 := by
  refine prime_of_cert 8360987 2 23 [2, 149, 28057] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_149
  · exact small_28057

theorem prime_50165923 : Nat.Prime 50165923 := by
  refine prime_of_cert 50165923 2 26 [2, 3, 8360987] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact prime_8360987

theorem prime_109267 : Nat.Prime 109267 := by
  refine prime_of_cert 109267 2 17 [2, 3, 18211] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_18211

theorem prime_1966807 : Nat.Prime 1966807 := by
  refine prime_of_cert 1966807 3 21 [2, 3, 3, 109267] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact prime_109267

theorem prime_5612846281303 : Nat.Prime 5612846281303 := by
  refine prime_of_cert 5612846281303 3 43 [2, 3, 13, 36587, 1966807] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_13
  · exact small_36587
  · exact prime_1966807

theorem prime_84395496284499229623254033 : Nat.Prime 84395496284499229623254033 := by
  refine prime_of_cert 84395496284499229623254033 5 87 [2, 2, 2, 2, 11, 13, 131, 50165923, 5612846281303] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_11
  · exact small_13
  · exact small_131
  · exact prime_50165923
  · exact prime_5612846281303

theorem prime_120179186709126902983513742993 : Nat.Prime 120179186709126902983513742993 := by
  refine prime_of_cert 120179186709126902983513742993 3 97 [2, 2, 2, 2, 89, 84395496284499229623254033] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_89
  · exact prime_84395496284499229623254033

theorem prime_137341 : Nat.Prime 137341 := by
  refine prime_of_cert 137341 18 18 [2, 2, 3, 3, 5, 7, 109] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_7
  · exact small_109

theorem prime_1491408717607 : Nat.Prime 1491408717607 := by
  refine prime_of_cert 1491408717607 3 41 [2, 3, 3, 29, 71, 293, 137341] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_29
  · exact small_71
  · exact small_293
  · exact prime_137341

theorem prime_476647 : Nat.Prime 476647 := by
  refine prime_of_cert 476647 13 19 [2, 3, 17, 4673] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_17
  · exact small_4673

theorem prime_612609603457 : Nat.Prime 612609603457 := by
  refine prime_of_cert 612609603457 5 40 [2, 2, 2, 2, 2, 2, 2, 3, 3347, 476647] (by decide) (by decide +kernel) ?_
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
  · exact small_3
  · exact small_3347
  · exact prime_476647

theorem prime_200935949933897 : Nat.Prime 200935949933897 := by
  refine prime_of_cert 200935949933897 3 48 [2, 2, 2, 41, 612609603457] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_41
  · exact prime_612609603457

theorem prime_1064159 : Nat.Prime 1064159 := by
  refine prime_of_cert 1064159 13 21 [2, 149, 3571] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_149
  · exact small_3571

theorem prime_2128319 : Nat.Prime 2128319 := by
  refine prime_of_cert 2128319 7 22 [2, 1064159] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact small_2
  · exact prime_1064159

theorem prime_4256639 : Nat.Prime 4256639 := by
  refine prime_of_cert 4256639 7 23 [2, 2128319] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact small_2
  · exact prime_2128319

theorem prime_2234757903503 : Nat.Prime 2234757903503 := by
  refine prime_of_cert 2234757903503 5 42 [2, 1913, 15511, 37657] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_1913
  · exact small_15511
  · exact small_37657

theorem prime_4188433 : Nat.Prime 4188433 := by
  refine prime_of_cert 4188433 10 22 [2, 2, 2, 2, 3, 71, 1229] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_71
  · exact small_1229

theorem prime_20020709741 : Nat.Prime 20020709741 := by
  refine prime_of_cert 20020709741 2 35 [2, 2, 5, 239, 4188433] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact small_239
  · exact prime_4188433

theorem prime_400414194821 : Nat.Prime 400414194821 := by
  refine prime_of_cert 400414194821 2 39 [2, 2, 5, 20020709741] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact prime_20020709741

theorem prime_31232307196039 : Nat.Prime 31232307196039 := by
  refine prime_of_cert 31232307196039 6 45 [2, 3, 13, 400414194821] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_13
  · exact prime_400414194821

theorem prime_4684846079405851 : Nat.Prime 4684846079405851 := by
  refine prime_of_cert 4684846079405851 2 53 [2, 3, 5, 5, 31232307196039] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_5
  · exact prime_31232307196039

theorem prime_57034811399347976721726973543287819857845741391551 : Nat.Prime 57034811399347976721726973543287819857845741391551 := by
  refine prime_of_cert 57034811399347976721726973543287819857845741391551 6 166 [2, 3, 5, 5, 13, 17, 277, 5717, 24379, 4256639, 2234757903503, 4684846079405851] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_5
  · exact small_13
  · exact small_17
  · exact small_277
  · exact small_5717
  · exact small_24379
  · exact prime_4256639
  · exact prime_2234757903503
  · exact prime_4684846079405851

theorem prime_297968944203544716575901889872036237935261750341463572996351910423 : Nat.Prime 297968944203544716575901889872036237935261750341463572996351910423 := by
  refine prime_of_cert 297968944203544716575901889872036237935261750341463572996351910423 5 218 [2, 13, 200935949933897, 57034811399347976721726973543287819857845741391551] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_13
  · exact prime_200935949933897
  · exact prime_57034811399347976721726973543287819857845741391551

theorem prime_14435454750020088047685444818571282397270727096595623715684950293729763357371155607979 : Nat.Prime 14435454750020088047685444818571282397270727096595623715684950293729763357371155607979 := by
  refine prime_of_cert 14435454750020088047685444818571282397270727096595623715684950293729763357371155607979 2 283 [2, 17, 23, 41539, 1491408717607, 297968944203544716575901889872036237935261750341463572996351910423] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_17
  · exact small_23
  · exact small_41539
  · exact prime_1491408717607
  · exact prime_297968944203544716575901889872036237935261750341463572996351910423

theorem prime_8948962207650232551656602815159153422162609644098354511344597187200057010413552439917934304191956942765446530386427345937963894309923928536070534607816947 : Nat.Prime 8948962207650232551656602815159153422162609644098354511344597187200057010413552439917934304191956942765446530386427345937963894309923928536070534607816947 := by
  refine prime_of_cert 8948962207650232551656602815159153422162609644098354511344597187200057010413552439917934304191956942765446530386427345937963894309923928536070534607816947 2 512 [2, 7, 61, 329430728783919403, 18335424362847464339, 120179186709126902983513742993, 14435454750020088047685444818571282397270727096595623715684950293729763357371155607979] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_7
  · exact small_61
  · exact prime_329430728783919403
  · exact prime_18335424362847464339
  · exact prime_120179186709126902983513742993
  · exact prime_14435454750020088047685444818571282397270727096595623715684950293729763357371155607979

theorem p_prime : Nat.Prime Spec.BrainpoolP512r1.p := by
  rw [show Spec.BrainpoolP512r1.p = 8948962207650232551656602815159153422162609644098354511344597187200057010413552439917934304191956942765446530386427345937963894309923928536070534607816947 by decide +kernel]
  exact prime_8948962207650232551656602815159153422162609644098354511344597187200057010413552439917934304191956942765446530386427345937963894309923928536070534607816947

end VG.Proof.BrainpoolP512r1
