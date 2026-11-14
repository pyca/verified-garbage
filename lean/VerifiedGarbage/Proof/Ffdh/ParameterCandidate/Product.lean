module

public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter candidates: trial division by a product of four primes

The candidate is reduced once modulo the product `M` of four of the table's
entries (`wordProd`), by Montgomery reduction by `2^64` word by word
(`redc64_math`, `prod_word_math`: `acc 2^(64 w) ≡ c (mod M)`), and each
prime `s ∣ M` is tested on `acc` alone (`acc_entry_math`). The arithmetic,
shared by the targets that do this. -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen
open VG.Proof.Bignum (pow64_succ)

/-- Montgomery reduction by `2^64` modulo the odd `M`, with `mv = −M⁻¹ mod
2^64`, of `acc + x`: below `M + 2`, and `(acc + x) 2^(−64) mod M`. -/
theorem redc64_math {M mv acc x : Nat} (hinv : (M * mv + 1) % 2 ^ 64 = 0)
    (hacc : acc < M + 2) (hx : x < 2 ^ 64) :
    ((acc + x) / 2 ^ 64 + (acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M / 2 ^ 64 +
        ((acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M % 2 ^ 64 + (acc + x) % 2 ^ 64) / 2 ^ 64) < M + 2 ∧
    ((acc + x) / 2 ^ 64 + (acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M / 2 ^ 64 +
        ((acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M % 2 ^ 64 + (acc + x) % 2 ^ 64) / 2 ^ 64) * 2 ^ 64 % M =
      (acc + x) % M := by
  generalize hX : acc + x = X
  have hXb : X < M + 2 + 2 ^ 64 := by omega_using [hacc, hx, hX]
  generalize hlo : X % 2 ^ 64 = lo
  have hlo' : lo < 2 ^ 64 := hlo ▸ Nat.mod_lt _ (by decide)
  generalize hq : lo * mv % 2 ^ 64 = q
  have hq' : q < 2 ^ 64 := hq ▸ Nat.mod_lt _ (by decide)
  -- q M + lo ≡ 0 (mod 2^64)
  have hz : (q * M + lo) % 2 ^ 64 = 0 := by
    rw [← hq, Nat.add_mod, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_comm mv M, ← Nat.add_mod]
    have : lo * (M * mv) + lo = lo * (M * mv + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rw [this, Nat.mul_mod, hinv, Nat.mul_zero, Nat.zero_mod]
  have e1 := Nat.div_add_mod X (2 ^ 64)
  have e2 := Nat.div_add_mod (q * M) (2 ^ 64)
  have e3 := Nat.div_add_mod (q * M % 2 ^ 64 + lo) (2 ^ 64)
  have hz' : (q * M % 2 ^ 64 + lo) % 2 ^ 64 = 0 := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; exact hz
  rw [hz', Nat.add_zero] at e3
  rw [hlo] at e1
  have hexact : (X / 2 ^ 64 + q * M / 2 ^ 64 + (q * M % 2 ^ 64 + lo) / 2 ^ 64) * 2 ^ 64 = X + q * M := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm (X / 2 ^ 64), Nat.mul_comm (q * M / 2 ^ 64),
      Nat.mul_comm ((q * M % 2 ^ 64 + lo) / 2 ^ 64), e3]
    omega_using [hinv, hacc, hX, hXb, hlo, hlo', hq, hq', hz, e1, e2, e3, hz']
  refine ⟨?_, ?_⟩
  · have hqM : q * M ≤ (2 ^ 64 - 1) * M := Nat.mul_le_mul_right _ (by omega_using [hq])
    have : (X / 2 ^ 64 + q * M / 2 ^ 64 + (q * M % 2 ^ 64 + lo) / 2 ^ 64) * 2 ^ 64 < (M + 2) * 2 ^ 64 := by
      rw [hexact]
      have : (2 ^ 64 - 1) * M + M = 2 ^ 64 * M := by
        rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by decide))]
      omega_using [hinv, hacc, hX, hXb, hlo, hq, hq', hz, e1, e2, e3, hz', hexact, hqM, this]
    exact Nat.lt_of_mul_lt_mul_right this
  · rw [hexact, Nat.add_mul_mod_self_right]


/-- Another word reduced: `acc 2^(64 j) ≡ c_j` carries on to `j + 1` words. -/
theorem prod_word_math {M acc r x V j : Nat} (h : r * 2 ^ 64 % M = (acc + x) % M)
    (hV : acc * 2 ^ (64 * j) % M = V % M) :
    r * 2 ^ (64 * (j + 1)) % M = (V + 2 ^ (64 * j) * x) % M := by
  calc r * 2 ^ (64 * (j + 1)) % M = r * 2 ^ 64 % M * (2 ^ (64 * j) % M) % M := by
        rw [pow64_succ, Nat.mul_comm (2 ^ (64 * j)) (2 ^ 64), ← Nat.mul_assoc, Nat.mul_mod]
    _ = (acc * 2 ^ (64 * j) + x * 2 ^ (64 * j)) % M := by rw [h, ← Nat.mul_mod, Nat.add_mul]
    _ = (acc * 2 ^ (64 * j) % M + x * 2 ^ (64 * j)) % M := (Nat.mod_add_mod _ _ _).symm
    _ = (V + 2 ^ (64 * j) * x) % M := by rw [hV, Nat.mod_add_mod, Nat.mul_comm x]

/-- The product of entries `4 i` to `4 i + 3` of the table. -/
def wordProd (i : Nat) : Nat := tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) * tabEntry (4 * i + 3)

theorem wordProd_facts {i : Nat} (hi : i < 256) : wordProd i % 2 = 1 ∧ wordProd i < 2 ^ 52 := by
  have b0 := tabEntry_facts (i := 4 * i) (by omega_using [hi])
  have b1 := tabEntry_facts (i := 4 * i + 1) (by omega_using [hi])
  have b2 := tabEntry_facts (i := 4 * i + 2) (by omega_using [hi])
  have b3 := tabEntry_facts (i := 4 * i + 3) (by omega_using [hi])
  unfold wordProd
  refine ⟨by rw [Nat.mul_mod, Nat.mul_mod (_ * _), Nat.mul_mod (tabEntry (4 * i)), b0.1, b1.1, b2.1, b3.1], ?_⟩
  have h01 : tabEntry (4 * i) * tabEntry (4 * i + 1) < 2 ^ 26 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le b0.2.2 (Nat.le_of_lt b1.2.2) (by omega_using [])) (by decide)
  have h012 : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) < 2 ^ 39 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le h01 (Nat.le_of_lt b2.2.2) (by omega_using [])) (by decide)
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le h012 (Nat.le_of_lt b3.2.2) (by omega_using [])) (by decide)

theorem dvd_wordProd {i j : Nat} (hj : j < 4) : tabEntry (4 * i + j) ∣ wordProd i := by
  unfold wordProd
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_using [hj]) with rfl | rfl | rfl | rfl
  · exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right _ _) _) _
  · exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_left _ _) _) _
  · exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_left _ _) _
  · exact Nat.dvd_mul_left _ _

/-- The reduced candidate: `acc 2^(64 (w + 1)) ≡ c (mod s)` from
`acc 2^(64 w) ≡ c (mod M)`, `s ∣ M` and `r 2^64 ≡ acc (mod s)`. -/
theorem acc_entry_math {s M acc r c w : Nat} (hd : s ∣ M) (hval : acc * 2 ^ (64 * w) % M = c % M)
    (hr : r * 2 ^ 64 % s = acc % s) : r * 2 ^ (64 * (w + 1)) % s = c % s := by
  have hv : acc * 2 ^ (64 * w) % s = c % s := by
    rw [← Nat.mod_mod_of_dvd _ hd, hval, Nat.mod_mod_of_dvd _ hd]
  rw [pow64_succ, Nat.mul_comm (2 ^ (64 * w)) (2 ^ 64), ← Nat.mul_assoc, Nat.mul_mod, hr, ← Nat.mul_mod, hv]

end VG.Proof.Ffdh.ParameterCandidate
