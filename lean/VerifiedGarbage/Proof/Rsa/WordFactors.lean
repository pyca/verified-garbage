module

public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: target-independent normalization facts, separate from the x86-64 dispatch proof

/-! # Normalized factors of a full-size balanced RSA modulus -/

@[expose] public section

namespace VG.Proof.Rsa

open VG VG.Proof.Bignum

/-- The modulus' first byte gives its full-size lower bound. -/
theorem os2ip_high {bs : List Byte} (hlen : 1 ≤ bs.length) (h : 128 ≤ (bs[0]'hlen).toNat) :
    2 ^ (8 * bs.length - 1) ≤ Spec.Rsa.os2ip bs := by
  cases bs with
  | nil => simp at hlen
  | cons b bs =>
    rw [os2ip_cons]
    simp only [List.getElem_cons_zero] at h
    have hb := Nat.mul_le_mul_right (256 ^ bs.length) h
    have he : 2 ^ (8 * (b :: bs).length - 1) = 128 * 256 ^ bs.length := by
      rw [pow256_eq, ← show 2 ^ 7 = 128 from rfl, ← Nat.pow_add]
      congr 1
      simp only [List.length_cons]
      omega_arith
    rw [he]
    omega_using [hb]

/-- If both factors fit `b` bits and their product fills `2b` bits, each
factor minus one has its high bit set. This also holds for composite factors. -/
theorem balanced_factor {P Q N b : Nat} (hb : 1 ≤ b) (hp : P < 2 ^ b) (hq : Q < 2 ^ b)
    (hn : 2 ^ (2 * b - 1) ≤ N) (he : P * Q = N) :
    2 ^ (b - 1) ≤ P - 1 ∧ 2 ^ (b - 1) ≤ Q - 1 := by
  have poweq : 2 ^ (2 * b - 1) = 2 ^ (b - 1) * 2 ^ b := by
    rw [← Nat.pow_add]; congr 1; omega_using [hb]
  have pos := Nat.two_pow_pos (b - 1)
  have one {A C : Nat} (hac : A * C = N) (hc : C < 2 ^ b) : 2 ^ (b - 1) ≤ A - 1 := by
    by_cases h : 2 ^ (b - 1) ≤ A - 1
    · exact h
    exfalso
    have ha : A ≤ 2 ^ (b - 1) := by omega_using [h]
    have hl := Nat.mul_le_mul_right C ha
    have hh := Nat.mul_lt_mul_of_pos_left hc pos
    rw [hac] at hl
    rw [poweq] at hn
    omega_using [hl, hh, hn]
  exact ⟨one he hq, one (by rw [Nat.mul_comm]; exact he) hp⟩

end VG.Proof.Rsa
