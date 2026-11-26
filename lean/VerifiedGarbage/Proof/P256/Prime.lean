module

import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Spec.P256
public import VerifiedGarbage.Proof.Framework.IsPrime

/-!
# The P-256 field prime `p` and group order `n` are prime

Pratt certificates (`Proof/Framework/Pratt.lean`), one theorem per prime of
the trees, for `p` and for `n`. Factors below `2^16` are prime by trial
division (`prime_small`).
-/

@[expose] public section

namespace VG.Proof.P256

open VG.Proof.Pratt

theorem small_2 : IsPrime 2 := prime_small _ (by decide +kernel)
theorem small_3 : IsPrime 3 := prime_small _ (by decide +kernel)
theorem small_5 : IsPrime 5 := prime_small _ (by decide +kernel)
theorem small_7 : IsPrime 7 := prime_small _ (by decide +kernel)
theorem small_11 : IsPrime 11 := prime_small _ (by decide +kernel)
theorem small_17 : IsPrime 17 := prime_small _ (by decide +kernel)
theorem small_19 : IsPrime 19 := prime_small _ (by decide +kernel)
theorem small_23 : IsPrime 23 := prime_small _ (by decide +kernel)
theorem small_29 : IsPrime 29 := prime_small _ (by decide +kernel)
theorem small_31 : IsPrime 31 := prime_small _ (by decide +kernel)
theorem small_41 : IsPrime 41 := prime_small _ (by decide +kernel)
theorem small_43 : IsPrime 43 := prime_small _ (by decide +kernel)
theorem small_53 : IsPrime 53 := prime_small _ (by decide +kernel)
theorem small_71 : IsPrime 71 := prime_small _ (by decide +kernel)
theorem small_107 : IsPrime 107 := prime_small _ (by decide +kernel)
theorem small_127 : IsPrime 127 := prime_small _ (by decide +kernel)
theorem small_131 : IsPrime 131 := prime_small _ (by decide +kernel)
theorem small_173 : IsPrime 173 := prime_small _ (by decide +kernel)
theorem small_197 : IsPrime 197 := prime_small _ (by decide +kernel)
theorem small_229 : IsPrime 229 := prime_small _ (by decide +kernel)
theorem small_257 : IsPrime 257 := prime_small _ (by decide +kernel)
theorem small_263 : IsPrime 263 := prime_small _ (by decide +kernel)
theorem small_311 : IsPrime 311 := prime_small _ (by decide +kernel)
theorem small_313 : IsPrime 313 := prime_small _ (by decide +kernel)
theorem small_337 : IsPrime 337 := prime_small _ (by decide +kernel)
theorem small_373 : IsPrime 373 := prime_small _ (by decide +kernel)
theorem small_641 : IsPrime 641 := prime_small _ (by decide +kernel)
theorem small_661 : IsPrime 661 := prime_small _ (by decide +kernel)
theorem small_1201 : IsPrime 1201 := prime_small _ (by decide +kernel)
theorem small_1297 : IsPrime 1297 := prime_small _ (by decide +kernel)
theorem small_1531 : IsPrime 1531 := prime_small _ (by decide +kernel)
theorem small_2411 : IsPrime 2411 := prime_small _ (by decide +kernel)
theorem small_3023 : IsPrime 3023 := prime_small _ (by decide +kernel)
theorem small_3407 : IsPrime 3407 := prime_small _ (by decide +kernel)
theorem small_3677 : IsPrime 3677 := prime_small _ (by decide +kernel)
theorem small_3769 : IsPrime 3769 := prime_small _ (by decide +kernel)
theorem small_4349 : IsPrime 4349 := prime_small _ (by decide +kernel)
theorem small_16879 : IsPrime 16879 := prime_small _ (by decide +kernel)
theorem small_17449 : IsPrime 17449 := prime_small _ (by decide +kernel)
theorem small_18169 : IsPrime 18169 := prime_small _ (by decide +kernel)
theorem small_38189 : IsPrime 38189 := prime_small _ (by decide +kernel)

theorem prime_65537 : IsPrime 65537 := by
  refine prime_of_cert 65537 3 17 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2

theorem prime_490463 : IsPrime 490463 := by
  refine prime_of_cert 490463 14 19 [2, 7, 53, 661] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_7
  · exact small_53
  · exact small_661

theorem prime_6700417 : IsPrime 6700417 := by
  refine prime_of_cert 6700417 5 23 [2, 2, 2, 2, 2, 2, 2, 3, 17449] (by decide) (by decide +kernel) ?_
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
  · exact small_2
  · exact small_3
  · exact small_17449

theorem prime_66417393611 : IsPrime 66417393611 := by
  refine prime_of_cert 66417393611 6 36 [2, 5, 53, 173, 197, 3677] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_53
  · exact small_173
  · exact small_197
  · exact small_3677

theorem prime_11290956913871 : IsPrime 11290956913871 := by
  refine prime_of_cert 11290956913871 13 44 [2, 5, 17, 66417393611] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_17
  · exact prime_66417393611

theorem prime_204061199 : IsPrime 204061199 := by
  refine prime_of_cert 204061199 11 28 [2, 11, 23, 107, 3769] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_11
  · exact small_23
  · exact small_107
  · exact small_3769

theorem prime_34282281433 : IsPrime 34282281433 := by
  refine prime_of_cert 34282281433 17 35 [2, 2, 2, 3, 7, 204061199] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_7
  · exact prime_204061199

theorem prime_704251 : IsPrime 704251 := by
  refine prime_of_cert 704251 2 20 [2, 3, 3, 5, 5, 5, 313] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_5
  · exact small_5
  · exact small_5
  · exact small_313

theorem prime_78283 : IsPrime 78283 := by
  refine prime_of_cert 78283 3 17 [2, 3, 3, 4349] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_4349

theorem prime_46076956964474543 : IsPrime 46076956964474543 := by
  refine prime_of_cert 46076956964474543 5 56 [2, 23, 18169, 78283, 704251] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_23
  · exact small_18169
  · exact prime_78283
  · exact prime_704251

theorem prime_774023187263532362759620327192479577272145303 : IsPrime 774023187263532362759620327192479577272145303 := by
  refine prime_of_cert 774023187263532362759620327192479577272145303 3 150 [2, 3, 3, 2411, 34282281433, 11290956913871, 46076956964474543] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_2411
  · exact prime_34282281433
  · exact prime_11290956913871
  · exact prime_46076956964474543

theorem prime_835945042244614951780389953367877943453916927241 : IsPrime 835945042244614951780389953367877943453916927241 := by
  refine prime_of_cert 835945042244614951780389953367877943453916927241 11 160 [2, 2, 2, 3, 3, 3, 5, 774023187263532362759620327192479577272145303] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_3
  · exact small_5
  · exact prime_774023187263532362759620327192479577272145303

theorem prime_115792089210356248762697446949407573530086143415290314195533631308867097853951 : IsPrime 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  refine prime_of_cert 115792089210356248762697446949407573530086143415290314195533631308867097853951 6 256 [2, 3, 5, 5, 17, 257, 641, 1531, 65537, 490463, 6700417, 835945042244614951780389953367877943453916927241] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_5
  · exact small_17
  · exact small_257
  · exact small_641
  · exact small_1531
  · exact prime_65537
  · exact prime_490463
  · exact prime_6700417
  · exact prime_835945042244614951780389953367877943453916927241

theorem prime_126241 : IsPrime 126241 := by
  refine prime_of_cert 126241 7 17 [2, 2, 2, 2, 2, 3, 5, 263] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_263

theorem prime_104471 : IsPrime 104471 := by
  refine prime_of_cert 104471 11 17 [2, 5, 31, 337] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_31
  · exact small_337

theorem prime_3969899 : IsPrime 3969899 := by
  refine prime_of_cert 3969899 2 22 [2, 19, 104471] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact small_19
  · exact prime_104471

theorem prime_1002328039319 : IsPrime 1002328039319 := by
  refine prime_of_cert 1002328039319 19 40 [2, 126241, 3969899] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact small_2
  · exact prime_126241
  · exact prime_3969899

theorem prime_9350987 : IsPrime 9350987 := by
  refine prime_of_cert 9350987 2 24 [2, 17, 229, 1201] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_17
  · exact small_229
  · exact small_1201

theorem prime_187019741 : IsPrime 187019741 := by
  refine prime_of_cert 187019741 2 28 [2, 2, 5, 9350987] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_5
  · exact prime_9350987

theorem prime_311245691 : IsPrime 311245691 := by
  refine prime_of_cert 311245691 2 29 [2, 5, 7, 17, 29, 29, 311] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_5
  · exact small_7
  · exact small_17
  · exact small_29
  · exact small_29
  · exact small_311

theorem prime_622491383 : IsPrime 622491383 := by
  refine prime_of_cert 622491383 5 30 [2, 311245691] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact small_2
  · exact prime_311245691

theorem prime_155317 : IsPrime 155317 := by
  refine prime_of_cert 155317 5 18 [2, 2, 3, 7, 43, 43] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_7
  · exact small_43
  · exact small_43

theorem prime_191039911 : IsPrime 191039911 := by
  refine prime_of_cert 191039911 3 28 [2, 3, 5, 41, 155317] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_5
  · exact small_41
  · exact prime_155317

theorem prime_208150935158385979 : IsPrime 208150935158385979 := by
  refine prime_of_cert 208150935158385979 2 58 [2, 3, 11, 43, 127, 3023, 191039911] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_3
  · exact small_11
  · exact small_43
  · exact small_127
  · exact small_3023
  · exact prime_191039911

theorem prime_2624747550333869278416773953 : IsPrime 2624747550333869278416773953 := by
  refine prime_of_cert 2624747550333869278416773953 7 92 [2, 2, 2, 2, 2, 2, 3, 3, 1297, 16879, 208150935158385979] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_3
  · exact small_1297
  · exact small_16879
  · exact prime_208150935158385979

theorem prime_115792089210356248762697446949407573529996955224135760342422259061068512044369 : IsPrime 115792089210356248762697446949407573529996955224135760342422259061068512044369 := by
  refine prime_of_cert 115792089210356248762697446949407573529996955224135760342422259061068512044369 7 256 [2, 2, 2, 2, 3, 71, 131, 373, 3407, 17449, 38189, 187019741, 622491383, 1002328039319, 2624747550333869278416773953] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_2
  · exact small_3
  · exact small_71
  · exact small_131
  · exact small_373
  · exact small_3407
  · exact small_17449
  · exact small_38189
  · exact prime_187019741
  · exact prime_622491383
  · exact prime_1002328039319
  · exact prime_2624747550333869278416773953

theorem p_prime : IsPrime Spec.P256.p := by
  rw [show Spec.P256.p =
    115792089210356248762697446949407573530086143415290314195533631308867097853951 by decide]
  exact prime_115792089210356248762697446949407573530086143415290314195533631308867097853951

theorem n_prime : IsPrime Spec.P256.n :=
  prime_115792089210356248762697446949407573529996955224135760342422259061068512044369

end VG.Proof.P256
