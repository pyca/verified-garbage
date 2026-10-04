import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Data.Int.ModEq
import Mathlib.FieldTheory.Finite.Basic

/-!
# RSA: what BoringSSL's checks protect against

Theorems about the specifications of `Spec/Rsa.lean`, stating the protection
its checks give:

* `privateChecked_ok`: the checked private operation releases only a result
  `y` with `y^e mod n` the input (`os2ip y < n` and `k` octets): a faulted
  computation is never released.
* `privateChecked_of_checkKey`: for every key `checkKey` (BoringSSL's
  `RSA_check_key`) accepts whose `p` and `q` are prime, the checked private
  operation of every input below `n` is `ok` with `c^d mod n`: the check
  against `e` never fails. (`RSA_check_key` does not check that `p` and `q`
  are prime; for a key it accepts with a composite factor, the check against
  `e` may fail, and the operation then releases nothing.)
* `publicOpChecked_eq`: the public operation within BoringSSL's limits is
  `publicOp` for an exponent within them, and `none` otherwise.
-/

namespace VG.Proof.Rsa

open VG.Spec.Rsa
open VG.Proof.Bignum (powMod_eq)

/-! ## Octet strings -/

theorem os2ip_snoc (l : List Byte) (b : Byte) : os2ip (l ++ [b]) = 256 * os2ip l + b.toNat := by
  simp only [os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem i2osp_succ (x k : Nat) : i2osp x (k + 1) = i2osp (x / 256) k ++ [BitVec.ofNat 8 x] := by
  simp only [i2osp, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    congr 3
    omega
  · rw [show k + 1 - 1 - k = 0 by omega, Nat.pow_zero, Nat.div_one]

/-- I2OSP then OS2IP keeps the low `k` octets. -/
theorem os2ip_i2osp (x k : Nat) : os2ip (i2osp x k) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [i2osp, os2ip, Nat.mod_one]
  | succ k ih =>
    rw [i2osp_succ, os2ip_snoc, ih, Nat.pow_succ', Nat.mod_mul, BitVec.toNat_ofNat]
    omega

theorem i2osp_length (x k : Nat) : (i2osp x k).length = k := by
  simp [i2osp]

/-- An integer of `k` octets is below `256^k`. -/
theorem lt_of_os2ip (bs : List Byte) : os2ip bs < 256 ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [os2ip]
  | append_singleton l b ih =>
    rw [os2ip_snoc, List.length_append, List.length_singleton, Nat.pow_succ]
    have := b.isLt
    simp only [Nat.reducePow] at this
    omega

/-! ## The CRT -/

/-- `h = (m₁ - m₂) qInv mod p` of `decryptCrt`, for `p > 0`, is below `p`. -/
theorem crt_h_lt {p : Nat} (hp : 0 < p) (x : Int) : (x % (p : Int)).toNat < p := by
  have h1 := Int.emod_nonneg x (by omega : (p : Int) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by omega : (0 : Int) < p)
  omega

/-- The result of `decryptCrt` is below `n`. -/
theorem decryptCrt_lt {n p q dP dQ qInv c m : Nat}
    (h : decryptCrt n p q dP dQ qInv c = some m) : m < n := by
  simp only [decryptCrt] at h
  split at h
  · rename_i hc
    obtain ⟨hcn, hpq, -⟩ := hc
    cases h
    have hp : 0 < p := Nat.pos_of_ne_zero fun h0 => by subst h0; omega
    have hq : 0 < q := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hpq; omega
    have hm₂ : powMod c dQ q < q := by rw [powMod_eq]; exact Nat.mod_lt _ hq
    have hh := crt_h_lt hp (((powMod c dP p : Nat) - (powMod c dQ q : Nat)) * (qInv : Int))
    -- `m₂ + q h ≤ (q - 1) + q (p - 1) = p q - 1`.
    have : q * (((powMod c dP p : Nat) - (powMod c dQ q : Nat)) * (qInv : Int) %
        (p : Int)).toNat ≤ q * (p - 1) := Nat.mul_le_mul_left _ (by omega)
    have : q * (p - 1) + q = p * q := by
      rw [Nat.mul_sub_one, Nat.mul_comm q p]; have := Nat.le_mul_of_pos_left q hp; omega
    omega
  · simp at h

/-! ## The checked private operation -/

/-- What `privateChecked` releases passes the check: `ok y` only for `y`,
`k` octets, with `os2ip y < n` and `(os2ip y)^e mod n` the input. -/
theorem privateChecked_ok {nB eB xB pB qB dPB dQB qInvB y : List Byte}
    (h : privateChecked nB eB xB pB qB dPB dQB qInvB = .ok y) :
    y.length = nB.length ∧ os2ip y < os2ip nB ∧
      os2ip y ^ os2ip eB % os2ip nB = os2ip xB := by
  simp only [privateChecked, decryptChecked] at h
  split at h
  · cases hd : decryptCrt (os2ip nB) (os2ip pB) (os2ip qB) (os2ip dPB) (os2ip dQB)
        (os2ip qInvB) (os2ip xB) with
    | none => simp [hd] at h
    | some m =>
      simp only [hd, Option.map_some] at h
      by_cases hpow : powMod m (os2ip eB) (os2ip nB) = os2ip xB
      · simp only [hpow, ite_true, Outcome.ok.injEq] at h
        subst h
        have hlt := decryptCrt_lt hd
        rw [powMod_eq] at hpow
        rw [i2osp_length, os2ip_i2osp, Nat.mod_eq_of_lt (Nat.lt_trans hlt (lt_of_os2ip nB))]
        exact ⟨rfl, hlt, hpow⟩
      · simp [hpow] at h
  · simp at h

/-! ## Keys `checkKey` accepts -/

/-- Fermat: modulo a prime `p`, powers with positive exponents congruent
modulo `p - 1` are congruent. -/
theorem pow_modEq_of_modEq {p a b : Nat} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≡ b [MOD p - 1]) (c : Nat) : c ^ a ≡ c ^ b [MOD p] := by
  by_cases hc : p ∣ c
  · exact (Nat.modEq_zero_iff_dvd.2 (Nat.dvd_trans hc (dvd_pow_self c ha.ne'))).trans
      (Nat.modEq_zero_iff_dvd.2 (Nat.dvd_trans hc (dvd_pow_self c hb.ne'))).symm
  · have hcop : c.Coprime p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hc)
    have hf : c ^ (p - 1) ≡ 1 [MOD p] := by
      have := Nat.ModEq.pow_totient hcop
      rwa [Nat.totient_prime hp] at this
    have key : ∀ x, c ^ x ≡ c ^ (x % (p - 1)) [MOD p] := by
      intro x
      have := (hf.pow (x / (p - 1))).mul_right (c ^ (x % (p - 1)))
      rwa [Nat.one_pow, Nat.one_mul, ← Nat.pow_mul, ← Nat.pow_add, Nat.div_add_mod] at this
    have hab' : a % (p - 1) = b % (p - 1) := hab
    exact (key a).trans (by rw [hab']; exact (key b).symm)

/-- The result of the CRT, `m₂ + q h`, is `m₁` modulo `p` if `q qInv ≡ 1`. -/
theorem crt_modEq_p {p q qInv m₁ m₂ : Nat} (hp : 0 < p) (hqi : q * qInv % p = 1) :
    m₂ + q * (((m₁ : Int) - m₂) * qInv % (p : Int)).toNat ≡ m₁ [MOD p] := by
  have hp1 : 1 < p := by
    rcases (show p = 1 ∨ 1 < p by omega) with h | h
    · subst h; rw [Nat.mod_one] at hqi; omega
    · exact h
  rw [← Int.natCast_modEq_iff]
  have hnn := Int.emod_nonneg (((m₁ : Int) - m₂) * qInv) (by omega : (p : Int) ≠ 0)
  have hqi' : (q : Int) * qInv ≡ 1 [ZMOD p] := by
    have : q * qInv ≡ 1 [MOD p] := by
      show q * qInv % p = 1 % p; rw [hqi, Nat.mod_eq_of_lt hp1]
    have := Int.natCast_modEq_iff.2 this
    push_cast at this
    exact this
  push_cast [Int.toNat_of_nonneg hnn]
  calc (m₂ : Int) + q * ((m₁ - m₂) * qInv % p)
      ≡ m₂ + q * ((m₁ - m₂) * qInv) [ZMOD p] := (Int.mod_modEq _ _).mul_left _ |>.add_left _
    _ = m₂ + (m₁ - m₂) * (q * qInv) := by ac_rfl
    _ ≡ m₂ + (m₁ - m₂) * 1 [ZMOD p] := (hqi'.mul_left _).add_left _
    _ = m₁ := by omega

/-- For a key `keyValid` accepts whose `p` and `q` are prime, the checked
private operation of every `c < n` passes the check and is `c^d mod n`. -/
theorem decryptChecked_of_keyValid {k n e d p q dP dQ qInv c : Nat}
    (hk : keyValid k n e d p q dP dQ qInv = true) (hp : p.Prime) (hq : q.Prime) (hc : c < n) :
    decryptChecked n e p q dP dQ qInv c = some (some (c ^ d % n)) := by
  simp only [keyValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at hk
  obtain ⟨-, -, -, -, -, hpq, hdep, hdeq, -, hedP, -, hedQ, hqip, hqi⟩ := hk
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  -- `p - 1` and `q - 1` are above 1, as `x mod 1 = 0`.
  have hp1 : 1 < p - 1 := by
    rcases (show p - 1 = 1 ∨ 1 < p - 1 by omega) with h | h
    · rw [h, Nat.mod_one] at hdep; omega
    · exact h
  have hq1 : 1 < q - 1 := by
    rcases (show q - 1 = 1 ∨ 1 < q - 1 by omega) with h | h
    · rw [h, Nat.mod_one] at hdeq; omega
    · exact h
  have one_p : 1 % (p - 1) = 1 := Nat.mod_eq_of_lt hp1
  have one_q : 1 % (q - 1) = 1 := Nat.mod_eq_of_lt hq1
  have pos : ∀ {x y m : Nat}, x * y % m = 1 → 0 < x ∧ 0 < y := by
    intro x y m h
    constructor <;> refine Nat.pos_of_ne_zero fun h0 => ?_ <;> simp [h0] at h
  -- `d ≡ dP (mod p - 1)` and `d ≡ dQ (mod q - 1)`: `d = d (e dP) = (d e) dP`.
  have hd_dP : d ≡ dP [MOD p - 1] := by
    have h1 : d * (e * dP) ≡ d * 1 [MOD p - 1] := Nat.ModEq.mul_left d (by
      show e * dP % (p - 1) = 1 % (p - 1); rw [hedP, one_p])
    have h2 : d * e * dP ≡ 1 * dP [MOD p - 1] := Nat.ModEq.mul_right dP (by
      show d * e % (p - 1) = 1 % (p - 1); rw [hdep, one_p])
    rw [Nat.mul_one] at h1; rw [Nat.one_mul, Nat.mul_assoc] at h2
    exact h1.symm.trans h2
  have hd_dQ : d ≡ dQ [MOD q - 1] := by
    have h1 : d * (e * dQ) ≡ d * 1 [MOD q - 1] := Nat.ModEq.mul_left d (by
      show e * dQ % (q - 1) = 1 % (q - 1); rw [hedQ, one_q])
    have h2 : d * e * dQ ≡ 1 * dQ [MOD q - 1] := Nat.ModEq.mul_right dQ (by
      show d * e % (q - 1) = 1 % (q - 1); rw [hdeq, one_q])
    rw [Nat.mul_one] at h1; rw [Nat.one_mul, Nat.mul_assoc] at h2
    exact h1.symm.trans h2
  have hcop : p.Coprime q :=
    Nat.coprime_comm.1 (Nat.coprime_of_mul_modEq_one qInv (by
      show q * qInv % p = 1 % p; rw [hqi, Nat.mod_eq_of_lt (by omega)]))
  -- The CRT's result is `c^d mod n`.
  have hdec : decryptCrt n p q dP dQ qInv c = some (c ^ d % n) := by
    have hif : decryptCrt n p q dP dQ qInv c = some (c ^ dQ % q + q *
        ((((c ^ dP % p : Nat) : Int) - (c ^ dQ % q : Nat)) * qInv % (p : Int)).toNat) := by
      simp only [decryptCrt, hc, hpq, hqip, and_self, ite_true, powMod_eq]
    have hm := decryptCrt_lt hif
    rw [hif, Option.some.injEq]
    have hmp : c ^ dQ % q + q * ((((c ^ dP % p : Nat) : Int) - (c ^ dQ % q : Nat)) * qInv %
        (p : Int)).toNat ≡ c ^ d [MOD p] :=
      (crt_modEq_p (by omega) hqi).trans
        ((Nat.mod_modEq _ _).trans (pow_modEq_of_modEq hp (pos hedP).2 (pos hdep).1 hd_dP.symm c))
    have hmq : c ^ dQ % q + q * ((((c ^ dP % p : Nat) : Int) - (c ^ dQ % q : Nat)) * qInv %
        (p : Int)).toNat ≡ c ^ d [MOD q] := by
      refine Nat.ModEq.trans ?_
        ((Nat.mod_modEq _ _).trans (pow_modEq_of_modEq hq (pos hedQ).2 (pos hdeq).1 hd_dQ.symm c))
      show _ % q = c ^ dQ % q % q
      rw [Nat.add_mul_mod_self_left]
    have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hmp, hmq⟩
    rw [hpq] at this
    rw [← Nat.mod_eq_of_lt hm]
    exact this
  -- It passes the check: `(c^d)^e = c^(d e) ≡ c` modulo `p` and `q`.
  have hcheck : powMod (c ^ d % n) e n = c := by
    rw [powMod_eq, ← Nat.pow_mod, ← Nat.pow_mul]
    have hp' : c ^ (d * e) ≡ c ^ 1 [MOD p] :=
      pow_modEq_of_modEq hp (Nat.mul_pos (pos hdep).1 (pos hdep).2) Nat.one_pos
        (by show d * e % (p - 1) = 1 % (p - 1); rw [hdep, one_p]) c
    have hq' : c ^ (d * e) ≡ c ^ 1 [MOD q] :=
      pow_modEq_of_modEq hq (Nat.mul_pos (pos hdeq).1 (pos hdeq).2) Nat.one_pos
        (by show d * e % (q - 1) = 1 % (q - 1); rw [hdeq, one_q]) c
    have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hp', hq'⟩
    rw [hpq, Nat.pow_one] at this
    rw [this, Nat.mod_eq_of_lt hc]
  rw [decryptChecked, hdec, Option.map_some]
  simp only [hcheck, ite_true]

/-- For every private key `checkKey` (BoringSSL's `RSA_check_key`) accepts
whose `p` and `q` are prime, the checked private operation of every input
below `n` passes the check against `e`, and is RSADP with `d`:
`c^d mod n`, as `k` octets. -/
theorem privateChecked_of_checkKey {nB eB dB pB qB dPB dQB qInvB xB : List Byte}
    (hk : checkKey nB eB dB pB qB dPB dQB qInvB = true) (hp : (os2ip pB).Prime)
    (hq : (os2ip qB).Prime) (hx : os2ip xB < os2ip nB) :
    privateChecked nB eB xB pB qB dPB dQB qInvB =
      .ok (i2osp (os2ip xB ^ os2ip dB % os2ip nB) nB.length) := by
  have hv : modulusValid (os2ip nB) nB.length ∧ exponentValid (os2ip eB) := by
    have hk' := hk
    simp only [checkKey, keyValid, Bool.and_eq_true] at hk'
    exact ⟨hk'.1.1.1.1.1.1.1.1.1.1.1.1.1, hk'.1.1.1.1.1.1.1.1.1.1.1.1.2⟩
  simp only [privateChecked, hv.1, hv.2, and_self, ite_true, decryptChecked_of_keyValid hk hp hq hx]

/-- For every private key `checkKey` accepts whose `p` and `q` are prime,
the checked private operation never fails its check against `e`. -/
theorem privateChecked_ne_fault {nB eB dB pB qB dPB dQB qInvB : List Byte} (xB : List Byte)
    (hk : checkKey nB eB dB pB qB dPB dQB qInvB = true) (hp : (os2ip pB).Prime)
    (hq : (os2ip qB).Prime) : privateChecked nB eB xB pB qB dPB dQB qInvB ≠ .fault := by
  by_cases hx : os2ip xB < os2ip nB
  · rw [privateChecked_of_checkKey hk hp hq hx]; nofun
  · intro hf
    simp [privateChecked, decryptChecked, decryptCrt, hx] at hf

/-! ## The public operation within BoringSSL's limits -/

/-- `publicOpChecked` is `publicOp` for an exponent within BoringSSL's
limits, and `none` otherwise. -/
theorem publicOpChecked_eq (nB eB xB : List Byte) :
    publicOpChecked nB eB xB =
      if exponentValid (os2ip eB) then publicOp nB eB xB else none := rfl

end VG.Proof.Rsa
