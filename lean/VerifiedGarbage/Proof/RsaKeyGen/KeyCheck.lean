import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# An RSA key from its primes: the checks

Once `d` is found and large, and `q` has an inverse modulo `p`, what
`keyFromPrimes` checks of the key (`bitLength n = nlen` and `keyValid`) is
what `vg_rsa_keygen_key` checks: `p` and `q` odd, the top bit of `n` set and
`e` a valid public exponent (`keyCheck_iff`). The rest follows: `L ≥ 2`
makes `p ≥ 3` and `q ≥ 2`, so `d < L < n`, `p, q < n`, and `d e ≡ 1` modulo
`L` is modulo `p − 1` and `q − 1` too.
-/

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen

/-- An integer of `2 pLen` octets below `256^(2 pLen)` reads back. -/
theorem os2ip_i2osp_lt {x k : Nat} (hx : x < 256 ^ k) : Spec.Rsa.os2ip (Spec.Rsa.i2osp x k) = x := by
  rw [Rsa.os2ip_i2osp, Nat.mod_eq_of_lt hx]

theorem bitLength_lt {n b : Nat} (h : bitLength n = b) : n < 2 ^ b := by
  unfold bitLength at h
  split at h
  · subst h; omega
  · rw [← h]; exact Nat.lt_log2_self

theorem le_of_bitLength {n b : Nat} (h : bitLength n = b + 1) : 2 ^ b ≤ n := by
  unfold bitLength at h
  split at h
  · omega
  · rename_i h0
    have := Nat.log2_self_le h0
    rwa [show n.log2 = b by omega] at this

theorem bitLength_of {n b : Nat} (h1 : 2 ^ b ≤ n) (h2 : n < 2 ^ (b + 1)) : bitLength n = b + 1 := by
  unfold bitLength
  have h0 : n ≠ 0 := by have := Nat.two_pow_pos b; omega
  rw [ite_eq_right h0, (Nat.log2_eq_iff h0).mpr ⟨h1, h2⟩]

theorem mul_odd {p q : Nat} : (p * q) % 2 = 1 ↔ p % 2 = 1 ∧ q % 2 = 1 := by
  rw [Nat.mul_mod]
  rcases Nat.mod_two_eq_zero_or_one p with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one q with h' | h' <;> simp [h, h']

/-- What `keyFromPrimes` checks of the key, once it has `d > 2^(8 pLen)`
and `qInv`, for `q ≤ p < 2^(8 pLen)` and `e < 2⁶⁴`. -/
theorem keyCheck_iff {pLen e p q d qInv : Nat} (hl1 : 32 ≤ pLen) (hl2 : pLen ≤ 512)
    (hp : p < 2 ^ (8 * pLen)) (hqp : q ≤ p) (he : e < 2 ^ 64)
    (hd : Spec.Rsa.inverse e (Nat.lcm (p - 1) (q - 1)) = some d) (hdb : 2 ^ (8 * pLen) < d)
    (hqi : Spec.Rsa.inverse q p = some qInv) :
    (bitLength (p * q) = 16 * pLen ∧
      keyValid ⟨p * q, e, d, p, q, d % (p - 1), d % (q - 1), qInv⟩ = true) ↔
    (p % 2 = 1 ∧ q % 2 = 1 ∧ 2 ^ (16 * pLen - 1) ≤ p * q ∧ Spec.Rsa.exponentValid e = true) := by
  obtain ⟨hed, hdL⟩ := inverse_some hd
  obtain ⟨hqq, hqiL⟩ := inverse_some hqi
  generalize hL : Nat.lcm (p - 1) (q - 1) = L at hed hdL
  -- `L ≥ 2`: `L = 0` has only the inverse 1.
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h
      rw [Nat.mod_zero] at hed
      have : d ≤ 1 := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · subst h0; omega
        · exact Nat.le_of_dvd (by decide) ⟨e, by rw [← hed, Nat.mul_comm]⟩
      have := Nat.one_lt_two_pow (n := 8 * pLen) (by omega)
      omega
    · exact h
  have hdL := hdL hL0
  have h2p : 2 ≤ 2 ^ (8 * pLen) := Nat.le_self_pow (by omega) 2 |>.trans' (by decide)
  have hq1 : q - 1 ≠ 0 := fun h => by rw [h, Nat.lcm_zero_right] at hL; omega
  have hLle : L ≤ (p - 1) * (q - 1) := by
    rw [← hL]
    exact Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.lcm_dvd_mul _ _)
  have hp3 : 3 ≤ p := by
    by_contra h
    have : (p - 1) * (q - 1) ≤ 1 := by
      have : p - 1 ≤ 1 := by omega
      have : q - 1 ≤ 1 := by omega
      exact Nat.mul_le_mul (by omega) (by omega) |>.trans (by decide)
    omega
  have hq2 : 2 ≤ q := by omega
  have hqi := hqiL (by omega)
  -- Sizes.
  have hn : p * q < 2 ^ (16 * pLen) := by
    rw [show 16 * pLen = 8 * pLen + 8 * pLen by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hp (by omega) (by omega)
  have hdn : d < p * q := by
    have : (p - 1) * (q - 1) < p * q :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega)
    omega
  have hpn : p < p * q := by have := Nat.mul_le_mul_left p hq2; omega
  have hqn : q < p * q := by have := Nat.mul_le_mul_right q hp3; omega
  have h256 : (256 : Nat) ^ (2 * pLen) = 2 ^ (16 * pLen) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega
  have he' : e < 256 ^ (2 * pLen) := by
    rw [h256]; exact Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) (by omega))
  have hdP : d % (p - 1) < p - 1 := Nat.mod_lt _ (by omega)
  have hdQ : d % (q - 1) < q - 1 := Nat.mod_lt _ (by omega)
  -- `keyValid` as numbers.
  have hkv : bitLength (p * q) = 16 * pLen →
      keyValid ⟨p * q, e, d, p, q, d % (p - 1), d % (q - 1), qInv⟩ =
        Spec.Rsa.keyValid (2 * pLen) (p * q) e d p q (d % (p - 1)) (d % (q - 1)) qInv := by
    intro hb
    have hlen : (bitLength (p * q) + 7) / 8 = 2 * pLen := by omega
    unfold keyValid Key.octets Key.len Spec.Rsa.checkKey
    dsimp only
    rw [hlen, Rsa.i2osp_length]
    have hlt : ∀ x, x < p * q → x < 256 ^ (2 * pLen) := fun x h => by omega
    rw [os2ip_i2osp_lt (by omega), os2ip_i2osp_lt he', os2ip_i2osp_lt (hlt _ hdn),
      os2ip_i2osp_lt (hlt _ hpn), os2ip_i2osp_lt (hlt _ hqn), os2ip_i2osp_lt (hlt _ (by omega)),
      os2ip_i2osp_lt (hlt _ (by omega)), os2ip_i2osp_lt (hlt _ (by omega))]
  have hdvd : ∀ m, m ∣ L → 1 < m → d * e % m = 1 := fun m hm h1 => by
    rw [← Nat.mod_mod_of_dvd _ hm, Nat.mul_comm, hed, Nat.mod_eq_of_lt h1]
  have hpd : p - 1 ∣ L := hL ▸ Nat.dvd_lcm_left _ _
  have hqd : q - 1 ∣ L := hL ▸ Nat.dvd_lcm_right _ _
  constructor
  · rintro ⟨hb, hk⟩
    rw [hkv hb] at hk
    simp only [Spec.Rsa.keyValid, Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hk
    refine ⟨(mul_odd.mp hk.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1).1,
      (mul_odd.mp hk.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1).2,
      le_of_bitLength (by rw [hb]; omega), hk.1.1.1.1.1.1.1.1.1.1.1.1.2⟩
  · rintro ⟨hpo, hqo, htop, hev⟩
    have hb : bitLength (p * q) = 16 * pLen :=
      (bitLength_of htop (by rw [show 16 * pLen - 1 + 1 = 16 * pLen by omega]; exact hn)).trans (by omega)
    refine ⟨hb, ?_⟩
    rw [hkv hb]
    have hq3 : 3 ≤ q := by omega
    have h511 := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 511 ≤ 16 * pLen - 1 by omega)
    have h8192 := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 16 * pLen ≤ 8192 by omega)
    simp only [Spec.Rsa.keyValid, Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, Nat.mul_mod_mod]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨mul_odd.mpr ⟨hpo, hqo⟩, ?_⟩, ?_⟩, ?_⟩, hev⟩, hdn⟩, hpn⟩, hqn⟩, trivial⟩,
      hdvd _ hpd (by omega)⟩, hdvd _ hqd (by omega)⟩, hdP⟩, ?_⟩, hdQ⟩, ?_⟩, hqi⟩, hqq⟩
    · exact Nat.le_trans h511 htop
    · exact Nat.lt_of_lt_of_le hn h8192
    · refine le_trans ?_ htop
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    · rw [Nat.mul_comm]; exact hdvd _ hpd (by omega)
    · rw [Nat.mul_comm]; exact hdvd _ hqd (by omega)

end VG.Proof.RsaKeyGen
