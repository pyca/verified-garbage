module

public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.Math

/-!
# FFDH: the domain buffer

The parameters of a domain buffer of `domain_len` octets at `dp`
(`domainOf`), from the octets of each component (`domainOf_p`, `_g`, `_q2`,
`_q3`); a valid domain's p is a valid modulus (`domainValid_mod`); and the
comparisons the code makes of a value with `p − 1` (`lt_pm1`).
-/

@[expose] public section

namespace VG.Proof.Ffdh

open VG VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)

theorem take_bytesAt (m : Mem) (dp : Addr) {k dl : Nat} (h : k ≤ dl) :
    (bytesAt m dp dl).take k = bytesAt m dp k := by
  have := VG.Proof.Dsa.bytesAt_slice m dp (offset := 0) (len := k) (by omega : 0 + k ≤ dl)
  simpa using this

theorem domainOf_p (m : Mem) (dp : Addr) {k dl : Nat} (h : 2 * k ≤ dl) :
    (domainOf k (bytesAt m dp dl)).p = os2ip (bytesAt m dp k) := by
  simp only [domainOf, take_bytesAt m dp (by omega : k ≤ dl)]

theorem domainOf_g (m : Mem) (dp : Addr) {k dl : Nat} (h : 2 * k ≤ dl) :
    (domainOf k (bytesAt m dp dl)).g = os2ip (bytesAt m (dp + BitVec.ofNat 64 k) k) := by
  simp only [domainOf, VG.Proof.Dsa.bytesAt_slice m dp (by omega : k + k ≤ dl)]

theorem domainOf_q2 (m : Mem) (dp : Addr) {k : Nat} (hk : 0 < k) :
    (domainOf k (bytesAt m dp (2 * k))).q = none := by
  simp only [domainOf, VG.Proof.Bignum.bytesAt_length]
  rw [ite_eq_right (show ¬ (2 * k = 3 * k) by omega)]

theorem domainOf_q3 (m : Mem) (dp : Addr) (k : Nat) :
    (domainOf k (bytesAt m dp (3 * k))).q = some (os2ip (bytesAt m (dp + BitVec.ofNat 64 (2 * k)) k)) := by
  simp only [domainOf, VG.Proof.Bignum.bytesAt_length, ↓reduceIte,
    VG.Proof.Dsa.bytesAt_slice m dp (by omega : 2 * k + k ≤ 3 * k)]

/-- For an odd `p`: `x < p − 1` iff `x` with its low bit set is below `p`. -/
theorem lt_pm1 {p : Nat} (hp : p % 2 = 1) (x : Nat) : 2 * (x / 2) + 1 < p ↔ x < p - 1 := by
  omega

/-- A valid domain's p, of `k` octets, is a valid modulus of `k` octets. -/
theorem domainValid_mod {k : Nat} {dom : List Byte} (hv : domainValid k dom = true) :
    Spec.Rsa.modulusValid (domainOf k dom).p k = true := by
  unfold domainValid parametersValid at hv
  unfold Spec.Rsa.modulusValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv ⊢
  obtain ⟨hv, h4⟩ := hv
  obtain ⟨hv, -⟩ := hv
  obtain ⟨hv, -⟩ := hv
  obtain ⟨hv, -⟩ := hv
  obtain ⟨⟨h1, h2⟩, h3⟩ := hv
  have hpos : (domainOf k dom).p ≠ 0 := by omega
  unfold Spec.RsaKeyGen.bitLength at h1 h2
  rw [ite_eq_right hpos] at h1 h2
  refine ⟨⟨⟨h3, ?_⟩, ?_⟩, h4⟩
  · have := (Nat.le_log2 (show (domainOf k dom).p ≠ 0 from hpos)).mp (by omega : 511 ≤ Nat.log2 _)
    exact this
  · have h5 := (fun B (hB : Nat.log2 (domainOf k dom).p + 1 ≤ B) => Nat.pow_le_pow_right (n := 2) (by decide) hB)
      8192 (by omega)
    have h6 := Nat.lt_log2_self (n := (domainOf k dom).p)
    omega

theorem bitLength_range {p : Nat} : (512 ≤ Spec.RsaKeyGen.bitLength p ∧ Spec.RsaKeyGen.bitLength p ≤ 8192) ↔
    (2 ^ 511 ≤ p ∧ p < 2 ^ 8192) := by
  unfold Spec.RsaKeyGen.bitLength
  by_cases hp : p = 0
  · subst hp
    rw [ite_eq_left rfl]
    have := Nat.two_pow_pos 511
    omega
  · rw [ite_eq_right hp]
    have h1 : 511 ≤ p.log2 ↔ 2 ^ 511 ≤ p := Nat.le_log2 hp
    have h2 : p.log2 < 8192 ↔ p < 2 ^ 8192 := Nat.log2_lt hp
    constructor
    · rintro ⟨a, b⟩; exact ⟨h1.mp (by omega), h2.mp (by omega)⟩
    · rintro ⟨a, b⟩; have := h1.mpr a; have := h2.mpr b; omega

/-- `domainValid`, as the code checks it: p a valid modulus, `1 < g < p − 1`,
and with q, q odd, `1 < q < p − 1`, `q ∣ p − 1` and `g^q mod p = 1`. -/
theorem domainValid_iff (k : Nat) (dom : List Byte) :
    domainValid k dom = true ↔ (Spec.Rsa.modulusValid (domainOf k dom).p k = true ∧
      (1 < (domainOf k dom).g ∧ (domainOf k dom).g < (domainOf k dom).p - 1) ∧
      ∀ q, (domainOf k dom).q = some q → (q % 2 = 1 ∧ 1 < q ∧ q < (domainOf k dom).p - 1) ∧
        ((domainOf k dom).p - 1) % q = 0 ∧ (domainOf k dom).g ^ q % (domainOf k dom).p = 1) := by
  unfold domainValid parametersValid Spec.Rsa.modulusValid
  generalize domainOf k dom = a
  obtain ⟨p, g, q⟩ := a
  have hb := bitLength_range (p := p)
  cases q with
  | none =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.and_true, reduceCtorEq, false_implies,
      implies_true, and_true]
    rw [hb]
    constructor
    · rintro ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩
      exact ⟨⟨⟨⟨c, a⟩, b⟩, f⟩, d, e⟩
    · rintro ⟨⟨⟨⟨c, a⟩, b⟩, f⟩, d, e⟩
      exact ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩
  | some q =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.some.injEq, forall_eq',
      VG.Proof.Bignum.powMod_eq]
    rw [hb]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, ⟨⟨⟨q2, qo⟩, ql⟩, qd⟩, qg⟩, f⟩
      exact ⟨⟨⟨⟨c, a⟩, b⟩, f⟩, ⟨d, e⟩, ⟨qo, by omega, ql⟩, qd, qg⟩
    · rintro ⟨⟨⟨⟨c, a⟩, b⟩, f⟩, ⟨d, e⟩, ⟨qo, q1, ql⟩, qd, qg⟩
      exact ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, ⟨⟨⟨by omega, qo⟩, ql⟩, qd⟩, qg⟩, f⟩

/-- A Montgomery reduction modulo an odd `Q` is zero iff `Q` divides its input. -/
theorem redc_zero {r Q X n : Nat} (hQ : Q % 2 = 1) (hr : r < Q) (h : r * 2 ^ n % Q = X % Q) :
    r = 0 ↔ X % Q = 0 := by
  constructor
  · rintro rfl; rw [← h]; simp
  · intro hx
    rw [hx] at h
    have hd : Q ∣ r * 2 ^ n := Nat.dvd_of_mod_eq_zero h
    have hc : Nat.Coprime Q (2 ^ n) := (VG.Proof.Bignum.coprime_pow2 hQ n).symm
    have := Nat.eq_zero_of_dvd_of_lt (hc.dvd_of_dvd_mul_right hd) hr
    exact this

/-- A number of `k` octets, its first not zero, has `⌈bitLength / 8⌉ = k`. -/
theorem octets_bitLength {p k : Nat} (hk : 0 < k) (hlo : 256 ^ (k - 1) ≤ p) (hhi : p < 256 ^ k) :
    (Spec.RsaKeyGen.bitLength p + 7) / 8 = k := by
  have e : ∀ n, (256 : Nat) ^ n = 2 ^ (8 * n) := fun n => by rw [Nat.pow_mul]
  rw [e] at hlo hhi
  have hp : p ≠ 0 := by have := Nat.two_pow_pos (8 * (k - 1)); omega
  unfold Spec.RsaKeyGen.bitLength
  rw [ite_eq_right hp]
  have h1 : 8 * (k - 1) ≤ p.log2 := (Nat.le_log2 hp).mpr hlo
  have h2 : p.log2 < 8 * k := (Nat.log2_lt hp).mpr hhi
  omega

/-- `exchangeOp` for a valid peer: z, unless it is 0, 1 or `p − 1`. -/
theorem exchangeOp_eq {a : Parameters} {X Y k : Nat} (hv : publicValid ⟨a, Y⟩ = true) (hp : 0 < a.p)
    (hk : (Spec.RsaKeyGen.bitLength a.p + 7) / 8 = k) :
    exchangeOp a X Y = if 1 < Y ^ X % a.p ∧ Y ^ X % a.p < a.p - 1 then
      some (Spec.Rsa.i2osp (Y ^ X % a.p) k) else none := by
  unfold exchangeOp exchange
  simp only [bne_self_eq_false, hv, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    VG.Proof.Bignum.powMod_eq, hk]
  by_cases h : 1 < Y ^ X % a.p ∧ Y ^ X % a.p < a.p - 1
  · have h1 : ¬ (Y ^ X % a.p ≤ 1 ∨ Y ^ X % a.p = a.p - 1) := by omega
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, h1, ↓reduceIte, h, and_self]
  · have := Nat.mod_lt (Y ^ X) hp
    have h1 : Y ^ X % a.p ≤ 1 ∨ Y ^ X % a.p = a.p - 1 := by omega
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, h1, ↓reduceIte, h]

/-- `privateStatus` for valid parameters. -/
theorem privateStatus_eq {a : Parameters} (hv : parametersValid a = true) (y x : Nat) :
    privateStatus a y x = if privateValid a x = false then 2 else
      if publicValid ⟨a, y⟩ = true ∧ a.g ^ x % a.p = y then 1 else 0 := by
  unfold privateStatus privateFrom publicFrom
  by_cases h1 : privateValid a x = false
  · simp [h1]
  · have h1' : privateValid a x = true := by simpa using h1
    by_cases h2 : publicValid ⟨a, y⟩ = true <;> by_cases h3 : a.g ^ x % a.p = y <;>
      simp [h1', h2, h3, hv, VG.Proof.Bignum.powMod_eq]

/-- `publicValid`, on the integers. -/
theorem publicValid_eq (a : Parameters) (y : Nat) :
    publicValid ⟨a, y⟩ = true ↔ (1 < y ∧ y < a.p - 1) ∧ ∀ q, a.q = some q → y ^ q % a.p = 1 := by
  unfold publicValid
  cases hq : a.q with
  | none => simp
  | some q => simp [VG.Proof.Bignum.powMod_eq]

end VG.Proof.Ffdh
