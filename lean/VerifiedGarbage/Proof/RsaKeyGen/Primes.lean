import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Impl.RsaKeyGen.Primes

/-!
# The sieve finds the specification's small primes

`Impl.RsaKeyGen.primes` is `Spec.RsaKeyGen.smallPrimes` (`primes_eq`): a
number from 2 to 8161 has a bit set in `compMask` iff it is `d k` with
`2 ≤ d ≤ 90` and `k ≥ 2`, iff it has a divisor from 2 to itself minus one.
-/

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Impl.RsaKeyGen

/-- A bit of a fold that ors in powers of two. -/
theorem testBit_foldl_or (P : Nat → Prop) [DecidablePred P] (f : Nat → Nat) (n : Nat) :
    ∀ (l : List Nat) (m : Nat), (l.foldl (fun m k => if P k then m ||| f k else m) m).testBit n = true ↔
      (m.testBit n = true ∨ ∃ k ∈ l, P k ∧ (f k).testBit n = true)
  | [], m => by simp
  | k :: l, m => by
    rw [List.foldl_cons, testBit_foldl_or P f n l]
    by_cases hk : P k
    · simp only [hk, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨k', hk', hP, h'⟩)
        · exact .inl h
        · exact .inr ⟨k, .inl rfl, hk, h⟩
        · exact .inr ⟨k', .inr hk', hP, h'⟩
      · rintro (h | ⟨k', (rfl | hk'), hP, h'⟩)
        · exact .inl (.inl h)
        · exact .inl (.inr h')
        · exact .inr ⟨k', hk', hP, h'⟩
    · simp only [hk, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (h | ⟨k', hk', hP, h'⟩)
        · exact .inl h
        · exact .inr ⟨k', .inr hk', hP, h'⟩
      · rintro (h | ⟨k', (rfl | hk'), hP, h'⟩)
        · exact .inl h
        · exact absurd hP hk
        · exact .inr ⟨k', hk', hP, h'⟩

theorem testBit_multMask (d n : Nat) :
    (multMask d).testBit n = true ↔ ∃ k, 2 ≤ k ∧ k ≤ 8162 / d ∧ d * k = n := by
  unfold multMask
  rw [testBit_foldl_or (fun k => 2 ≤ k) (fun k => 2 ^ (d * k)) n]
  simp only [Nat.zero_testBit, Bool.false_eq_true, List.mem_range, decide_eq_true_eq,
    Nat.testBit_two_pow, false_or]
  constructor
  · rintro ⟨k, hk, h2, h⟩; exact ⟨k, h2, by omega, h⟩
  · rintro ⟨k, h2, hk, h⟩; exact ⟨k, by omega, h2, h⟩

theorem testBit_compMask (n : Nat) :
    compMask.testBit n = true ↔ ∃ d k, 2 ≤ d ∧ d < 91 ∧ 2 ≤ k ∧ k ≤ 8162 / d ∧ d * k = n := by
  unfold compMask
  rw [testBit_foldl_or (fun d => 2 ≤ d) multMask n]
  simp only [Nat.zero_testBit, Bool.false_eq_true, List.mem_range, testBit_multMask, false_or]
  constructor
  · rintro ⟨d, hd, h2, k, hk⟩; exact ⟨d, k, h2, hd, hk⟩
  · rintro ⟨d, k, h2, hd, hk⟩; exact ⟨d, hd, h2, k, hk⟩

/-- Trial division by every number below `n` is the sieve, below 8162. -/
theorem smallPrime_eq {n : Nat} (hn : n < 8162) :
    smallPrime n = (decide (2 ≤ n) && !compMask.testBit n) := by
  unfold smallPrime
  by_cases h2 : 2 ≤ n
  · simp only [h2, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      Bool.not_eq_true', Bool.eq_false_iff, testBit_compMask]
    constructor
    · rintro h ⟨d, k, hd2, -, hk2, -, rfl⟩
      rcases h d (by
        have : d * 2 ≤ d * k := Nat.mul_le_mul_left d hk2
        omega) with h | h
      · omega
      · exact h (Nat.mul_mod_right d k)
    · intro h d hd
      by_cases hd2 : d < 2
      · exact .inl hd2
      refine .inr fun hm => h ?_
      have hdk : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)
      generalize n / d = k at hdk
      rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
      · rw [Nat.mul_zero] at hdk; omega
      · rw [Nat.mul_one] at hdk; omega
      have hle : ∀ a b, a * b = n → b ≤ 8162 / a := fun a b hab =>
        (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hab; omega)).mpr
          (by rw [Nat.mul_comm]; omega)
      rcases Nat.lt_or_ge d 91 with hd91 | hd91
      · exact ⟨d, k, by omega, hd91, hk2, hle d k hdk, hdk⟩
      · have hk91 : k < 91 := by
          rcases Nat.lt_or_ge k 91 with h | h
          · exact h
          · have : 91 * 91 ≤ d * k := Nat.mul_le_mul hd91 h
            omega
        exact ⟨k, d, hk2, hk91, by omega, hle k d (by rw [Nat.mul_comm]; exact hdk),
          by rw [Nat.mul_comm]; exact hdk⟩
  · simp [h2]

/-- The sieve's primes are the specification's. -/
theorem primes_eq : primes = smallPrimes := by
  unfold primes smallPrimes
  refine List.filter_congr fun n hn => ?_
  rw [smallPrime_eq (List.mem_range.mp hn)]

end VG.Proof.RsaKeyGen

