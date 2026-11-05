module

public import VerifiedGarbage.Spec.Ffdh

/-!
# Miller–Rabin as BoringSSL computes it is FIPS 186-5 B.3.1

**Trusted** (as every file in `Spec/`), but only for what its theorems
state: their proofs are checked by the kernel, so a reviewer reads the
statements, not the proofs.

RSA key generation and DSA parameter generation (`RsaKeyGen.primalityTest`,
`Dsa.probablePrime`) test their candidates as BoringSSL does
(`BN_primality_test`): trial division (`RsaKeyGen.obviouslyComposite`),
witnesses drawn from 64-bit words and forced into range
(`RsaKeyGen.witness`), and a squaring loop of a fixed length
(`RsaKeyGen.mrIteration`, `RsaKeyGen.mrSquarings`). FFDH parameter
generation uses instead the plain round of FIPS 186-5 B.3.1, `Ffdh.mrRound`:
for `w − 1 = 2^a m` with `m` odd, `w` passes for the witness `b` if
`z = b^m mod w` is 1, or `z^(2^j) mod w` is `w − 1` for some `j < a`
(steps 4.3–4.7). The theorems here relate the two forms, so that what RSA
and DSA require is B.3.1's test:

* `mrIteration_eq_mrRound`: for the odd `w > 1` (the only `w` it is used
  for) and every witness, BoringSSL's round (`mrIteration` of `w − 1`
  split by `splitTwos`) gives B.3.1's verdict, `Ffdh.mrRound`.
* `witness_range`: every witness `RsaKeyGen.witness` gives, uniform or
  forced, is one B.3.1 step 4.2 allows, in `[2, w − 2]`.
* `obviouslyComposite_dvd`: trial division only rejects a candidate with a
  divisor other than 1 and itself, a composite.

What these leave as policy, a choice BoringSSL and OpenSSL make that is
not FIPS 186-5's: which random octets give a witness (`RsaKeyGen.witness`,
`witnessBytes`, of which only the uniform ones count towards the rounds), and
how many rounds are run (`RsaKeyGen.checksForSize` and `blindedChecks` for
RSA, `Dsa.primeChecks` and `Ffdh.primeChecks` for DSA and FFDH), which are
BoringSSL's and OpenSSL's tables, not the minimum counts FIPS 186-5 tabulates
(FIPS 186-4's Table C.1); a reviewer checks them against those libraries.
Nothing here bounds the probability that a composite passes.
-/

@[expose] public section

namespace VG.Spec.MillerRabin

open VG.Spec.Rsa (powMod splitTwos)
open VG.Spec.RsaKeyGen (mrSquarings mrIteration bitLength witness obviouslyComposite smallPrimes
  smallPrime)

/-! ## The squaring loop -/

/-- `z` squared `t` times modulo `w`. -/
def sqIter (w z : Nat) : Nat → Nat
  | 0 => z
  | t + 1 => sqIter w z t * sqIter w z t % w

theorem sqIter_succ' (w z t : Nat) : sqIter w z (t + 1) = sqIter w (z * z % w) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [sqIter, ih, sqIter]

theorem sqIter_one (w : Nat) (hw : 2 ≤ w) : ∀ t, sqIter w 1 t = 1
  | 0 => rfl
  | t + 1 => by rw [sqIter, sqIter_one w hw t, Nat.one_mul, Nat.mod_eq_of_lt (by omega)]

/-- With `possible` set, the squarings end with it. -/
theorem mrSquarings_true (w a : Nat) : ∀ fuel j z, mrSquarings w a fuel j z true = true
  | 0, _, _ => rfl
  | fuel + 1, j, z => by
    simp only [mrSquarings, Bool.not_true, Bool.false_eq_true, and_false, ↓reduceIte, Bool.true_or,
      Bool.and_false]
    exact mrSquarings_true w a fuel (j + 1) _

/-- The squarings from `j ≤ a`, with `z` the value after `j − 1` of them:
`possible`, or one of the next `a − j` squares is `w − 1`. -/
theorem mrSquarings_iff (w a : Nat) (hw : 3 ≤ w) :
    ∀ fuel j z possible, 1 ≤ j → j ≤ a → a ≤ fuel + j - 1 →
      (mrSquarings w a fuel j z possible = true ↔
        (possible = true ∨ ∃ t, 1 ≤ t ∧ t ≤ a - j ∧ sqIter w z t = w - 1))
  | 0, j, _, _, h1, hja, haf => by omega
  | fuel + 1, j, z, possible, h1, hja, haf => by
    rcases Nat.lt_or_ge j a with hlt | hge
    · have hne : ¬ (j = a ∧ (!possible) = true) := fun h => by omega
      simp only [mrSquarings, hne, ↓reduceIte]
      by_cases hz : (z * z % w == 1 && !(possible || z * z % w == w - 1)) = true
      · simp only [hz, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
          beq_eq_false_iff_ne] at hz
        obtain ⟨hz1, hp, -⟩ := hz
        simp only [hp, Bool.false_or, beq_iff_eq, Bool.false_eq_true, false_or]
        constructor
        · intro h; omega
        · rintro ⟨t, ht, _, he⟩
          obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          rw [sqIter_succ', hz1, sqIter_one w (by omega)] at he
          omega
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        rw [mrSquarings_iff w a hw fuel (j + 1) _ _ (by omega) (by omega) (by omega)]
        simp only [Bool.or_eq_true, beq_iff_eq]
        constructor
        · rintro ((hp | he) | ⟨t, ht1, ht2, he⟩)
          · exact .inl hp
          · exact .inr ⟨1, Nat.le_refl _, by omega, by rw [sqIter, sqIter]; exact he⟩
          · exact .inr ⟨t + 1, by omega, by omega, by rw [sqIter_succ']; exact he⟩
        · rintro (hp | ⟨t, ht1, ht2, he⟩)
          · exact .inl (.inl hp)
          · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
            rcases t' with _ | t'
            · exact .inl (.inr (by rw [sqIter, sqIter] at he; exact he))
            · exact .inr ⟨t' + 1, by omega, by omega, by rw [← sqIter_succ']; exact he⟩
    · have hj : j = a := by omega
      subst hj
      cases possible
      · simp only [mrSquarings, Bool.not_false, and_self, ↓reduceIte, Bool.false_eq_true, false_or]
        constructor
        · intro h; exact absurd h (by decide)
        · rintro ⟨t, h1, h2, _⟩; omega
      · simp [mrSquarings_true]

/-! ## Powers -/

/-- `powMod` of an even exponent `2 e > 0`. -/
theorem powMod_double (b e w : Nat) (he : 0 < e) :
    powMod b (2 * e) w = powMod b e w * powMod b e w % w := by
  rw [powMod]
  simp only [show 2 * e ≠ 0 by omega, ↓reduceIte, show 2 * e / 2 = e by omega,
    show 2 * e % 2 = 0 by omega]

/-- `z^(2^t) mod w` is `z` squared `t` times, for `z < w`. -/
theorem powMod_two_pow {w z : Nat} (hw : 2 ≤ w) (hz : z < w) :
    ∀ t, powMod z (2 ^ t) w = sqIter w z t
  | 0 => by
    rw [Nat.pow_zero, powMod]
    simp only [Nat.one_ne_zero, ↓reduceIte, Nat.reduceDiv, Nat.one_mod, ↓reduceIte, sqIter]
    rw [powMod]
    simp only [↓reduceIte, Nat.mod_eq_of_lt (show 1 < w by omega), Nat.one_mul,
      Nat.mod_eq_of_lt hz]
  | t + 1 => by
    rw [sqIter, ← powMod_two_pow hw hz t, Nat.pow_succ, Nat.mul_comm]
    exact powMod_double z _ w (Nat.two_pow_pos _)

theorem splitTwos_spec : ∀ n, 0 < n → n = (splitTwos n).2 * 2 ^ (splitTwos n).1 ∧ (splitTwos n).2 % 2 = 1
  | n, hn => by
    rw [splitTwos]
    by_cases h : n = 0 ∨ n % 2 = 1
    · simp only [h, ↓reduceIte, Nat.pow_zero, Nat.mul_one, true_and]; omega
    · simp only [h, ↓reduceIte]
      obtain ⟨h1, h2⟩ := splitTwos_spec (n / 2) (by omega)
      refine ⟨?_, h2⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← h1]; omega
termination_by n => n
decreasing_by omega

/-! ## The round -/

/-- BoringSSL's round, `bn_miller_rabin_iteration` (`RsaKeyGen.mrIteration`,
with its fixed-length squaring loop `mrSquarings`), gives FIPS 186-5
B.3.1's verdict (`Ffdh.mrRound`, steps 4.3–4.7) for every odd `w > 1` and
every witness `b`, with `w − 1 = 2^a m` as `splitTwos` splits it. -/
theorem mrIteration_eq_mrRound {w : Nat} (hw : 1 < w) (hodd : w % 2 = 1) (b : Nat) :
    mrIteration w (splitTwos (w - 1)).1 (splitTwos (w - 1)).2 b = Ffdh.mrRound w b := by
  have hw3 : 3 ≤ w := by omega
  obtain ⟨hsplit, hmodd⟩ := splitTwos_spec (w - 1) (by omega)
  unfold Ffdh.mrRound
  generalize splitTwos (w - 1) = s at hsplit hmodd ⊢
  obtain ⟨a, m⟩ := s
  simp only at hsplit hmodd ⊢
  have ha : 1 ≤ a := by
    rcases a with _ | a
    · rw [Nat.pow_zero, Nat.mul_one] at hsplit; omega
    · omega
  have haw : a ≤ bitLength w - 1 := by
    have h2 : 2 ^ a ≤ w := by
      have : 2 ^ a ≤ m * 2 ^ a := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have := (Nat.le_log2 (show w ≠ 0 by omega)).2 h2
    simp only [bitLength, show w ≠ 0 by omega, ↓reduceIte]
    omega
  have hz : powMod b m w < w := by
    rw [powMod]; split <;> (try split) <;> exact Nat.mod_lt _ (by omega)
  apply Bool.eq_iff_iff.2
  unfold mrIteration
  simp only
  rw [mrSquarings_iff w a hw3 _ 1 _ _ (Nat.le_refl _) ha (by omega)]
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range,
    powMod_two_pow (by omega) hz]
  constructor
  · rintro ((h | h) | ⟨t, _, ht, he⟩)
    · exact .inl h
    · exact .inr ⟨0, ha, h⟩
    · exact .inr ⟨t, by omega, he⟩
  · rintro (h | ⟨t, ht, he⟩)
    · exact .inl (.inl h)
    · rcases t with _ | t
      · exact .inl (.inr he)
      · exact .inr ⟨t + 1, by omega, by omega, he⟩

/-! ## The witnesses -/

/-- Every witness `RsaKeyGen.witness` gives for `w1 = w − 1`, uniform or
forced into range, is in `[2, w − 2]`, as B.3.1 step 4.2 requires, for every
`w ≥ 5` (an odd `w > 3`, the only `w` it is drawn for). -/
theorem witness_range {w1 : Nat} (hw : 4 ≤ w1) (x : Nat) :
    2 ≤ (witness w1 x).1 ∧ (witness w1 x).1 < w1 := by
  unfold witness
  simp only
  split
  · rename_i h; exact h
  · simp only
    have hl : bitLength w1 = w1.log2 + 1 := by simp [bitLength, show w1 ≠ 0 by omega]
    have hlog : 2 ≤ w1.log2 := (Nat.le_log2 (show w1 ≠ 0 by omega)).2 (by omega)
    rw [hl, Nat.add_sub_cancel]
    refine ⟨?_, ?_⟩
    · have hb : (((x % 2 ^ (w1.log2 + 1)) ||| 2) % 2 ^ w1.log2).testBit 1 = true := by
        rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
        simp only [decide_eq_true (show 1 < w1.log2 by omega), Bool.true_and]
        exact Bool.or_eq_true_iff.2 (.inr (by decide))
      apply Nat.le_of_not_lt
      intro hlt
      rw [Nat.testBit_lt_two_pow (show _ < 2 ^ 1 by omega)] at hb
      exact absurd hb (by decide)
    · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.log2_self_le (show w1 ≠ 0 by omega))

/-! ## Trial division -/

/-- Trial division (`bn_odd_number_is_obviously_composite`) rejects only a
candidate `c > 0` with a divisor other than 1 and `c`: a composite. -/
theorem obviouslyComposite_dvd {bits c : Nat} (hc : 0 < c) (h : obviouslyComposite bits c = true) :
    ∃ s, 1 < s ∧ s < c ∧ s ∣ c := by
  unfold obviouslyComposite at h
  obtain ⟨s, hs, hd⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hd
  have hmem : s ∈ smallPrimes := List.mem_of_mem_take (List.mem_of_mem_drop hs)
  have hp : smallPrime s = true := (List.mem_filter.1 hmem).2
  have h2 : 2 ≤ s := by
    unfold smallPrime at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.1
  have hdvd : s ∣ c := Nat.dvd_of_mod_eq_zero hd.1
  exact ⟨s, by omega, Nat.lt_of_le_of_ne (Nat.le_of_dvd hc hdvd) (Ne.symm hd.2), hdvd⟩

end VG.Spec.MillerRabin
