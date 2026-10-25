module

public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.PowLit

/-! # The checks of an RSA key on PPC64LE: the mask is the spec's

`ck_bits`, `cck_bits`: with the products as `mulMod` computes them (`e` over
33 bits, `q` over all its bits, each known when its factor is below its
modulus and twice the modulus fits), the mask the checks compute is
`keyValid` and `crtKeyValid`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG.Spec.Rsa

theorem fit_two {k w p : Nat} (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (32 * w)) (hp : p < 256 ^ (k - 1)) :
    2 * p ≤ 2 ^ (32 * w) := by
  have : 256 ^ k = 256 * 256 ^ (k - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  omega

theorem ck_bits {k n e d p q dP dQ qI w : Nat} (hm : modulusValid n k = true) (he : exponentValid e = true)
    (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1)) (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (32 * w))
    {X₁ X₂ R₁ R₂ R₃ Y₁ Y₂ : Nat} (hX : 0 < p → X₁ = n / p ∧ X₂ = n % p)
    (hR₁ : dP < 2 * (p / 2) → 2 * (2 * (p / 2)) ≤ 2 ^ (32 * w) → R₁ = e % 2 ^ 33 * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → 2 * (2 * (q / 2)) ≤ 2 ^ (32 * w) → R₂ = e % 2 ^ 33 * dQ % (2 * (q / 2)))
    (hR₃ : qI < p → 2 * p ≤ 2 ^ (32 * w) → R₃ = q * qI % p)
    (hY₁ : 0 < 2 * (p / 2) → Y₁ = d % (2 * (p / 2))) (hY₂ : 0 < 2 * (q / 2) → Y₂ = d % (2 * (q / 2))) :
    keyValid k n e d p q dP dQ qI = VG.Proof.Rsa.keyBits' n d p q dP dQ qI X₁ X₂ R₁ R₂ R₃ Y₁ Y₂ := by
  have he' : e < 2 ^ 33 := by
    simp only [exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he; exact he.2
  have fp := fit_two hk hw hp
  have fq := fit_two hk hw hq
  refine VG.Proof.Rsa.keyValid_bits hm he hp hq hX (fun h => ?_) (fun h => ?_) (fun h => ?_) hY₁ hY₂
  · rw [hR₁ h (Nat.le_trans (by omega : 2 * (2 * (p / 2)) ≤ 2 * p) fp), Nat.mod_eq_of_lt he']
  · rw [hR₂ h (Nat.le_trans (by omega : 2 * (2 * (q / 2)) ≤ 2 * q) fq), Nat.mod_eq_of_lt he']
  · rw [hR₃ h fp]

theorem cck_bits {k n e p q dP dQ qI w : Nat} (hm : modulusValid n k = true) (he : exponentValid e = true)
    (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1)) (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (32 * w))
    {X₁ X₂ R₁ R₂ R₃ : Nat} (hX : 0 < p → X₁ = n / p ∧ X₂ = n % p)
    (hR₁ : dP < 2 * (p / 2) → 2 * (2 * (p / 2)) ≤ 2 ^ (32 * w) → R₁ = e % 2 ^ 33 * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → 2 * (2 * (q / 2)) ≤ 2 ^ (32 * w) → R₂ = e % 2 ^ 33 * dQ % (2 * (q / 2)))
    (hR₃ : qI < p → 2 * p ≤ 2 ^ (32 * w) → R₃ = q * qI % p) :
    crtKeyValid k n e p q dP dQ qI = VG.Proof.Rsa.crtBits p q dP dQ qI X₁ X₂ R₁ R₂ R₃ := by
  have he' : e < 2 ^ 33 := by
    simp only [exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he; exact he.2
  have fp := fit_two hk hw hp
  have fq := fit_two hk hw hq
  refine VG.Proof.Rsa.crtKeyValid_bits hm he hp hq hX (fun h => ?_) (fun h => ?_) (fun h => ?_)
  · rw [hR₁ h (Nat.le_trans (by omega : 2 * (2 * (p / 2)) ≤ 2 * p) fp), Nat.mod_eq_of_lt he']
  · rw [hR₂ h (Nat.le_trans (by omega : 2 * (2 * (q / 2)) ≤ 2 * q) fq), Nat.mod_eq_of_lt he']
  · rw [hR₃ h fp]

/-- A number of `l < k` bytes is below `256^(k - 1)`. -/
theorem lt_pow_of_len (bs : List Byte) {k : Nat} (h : bs.length < k) : os2ip bs < 256 ^ (k - 1) :=
  Nat.lt_of_lt_of_le (VG.Proof.Rsa.lt_of_os2ip bs) (Nat.pow_le_pow_right (by decide) (by omega))

/-- A number of `a` bytes is below `2^(8 a)`. -/
theorem lt_pow8_of_len (bs : List Byte) {a : Nat} (h : bs.length = a) : os2ip bs < 2 ^ (8 * a) := by
  rw [Nat.pow_mul, ← h]; exact VG.Proof.Rsa.lt_of_os2ip bs

/-- `2^(32 w)` for `w = ⌈k / 4⌉` is at least `256^k`. -/
theorem pow_kw (k : Nat) : 256 ^ k ≤ 2 ^ (32 * ((k + 3) / 4)) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)

end VG.Proof.Rsa.PPC64LE.KeyCheck
