module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Bounded comparisons used by the RSA modulus validator -/

@[expose] public section

namespace VG.Proof.Bignum
open VG

theorem bounded_sub_sign (x : BitVec 32) {c : Nat}
    (hx : x.toNat < 2 ^ 31) (hc : c ≤ 2 ^ 31) :
    (x - BitVec.ofNat 32 c) >>> 31 = if x.toNat < c then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32)]
  split <;> simp only [show (1 : BitVec 32).toNat = 1 from rfl,
    show (0 : BitVec 32).toNat = 0 from rfl] <;> omega

theorem parity_word (x : BitVec 32) : x &&& 1 = BitVec.ofNat 32 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

theorem threshold_word (k first : BitVec 32) (hk : 64 ≤ k.toNat) (hk' : k.toNat ≤ 1024)
    (hf : first.toNat < 256) :
    (((k - 64) <<< 8) + first).toNat = (k.toNat - 64) * 256 + first.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_sub]
  simp only [show (64 : BitVec 32).toNat = 64 from rfl, Nat.shiftLeft_eq]
  omega

theorem modulusCheck_value (first last k : BitVec 32)
    (hf : first.toNat < 256) (hk : 64 ≤ k.toNat) (hk' : k.toNat ≤ 1024) :
    (((first - 1) >>> 31 ||| ((last &&& (1 : BitVec 32)) ^^^ (1 : BitVec 32)) |||
      (((((k - 64) <<< 8) + first) - 128) >>> 31)) == 0) =
      !(decide (first.toNat < 1) || decide (last.toNat % 2 < 1) ||
        decide ((k.toNat - 64) * 256 + first.toNat < 128)) := by
  have ht := threshold_word k first hk hk' hf
  have top : ((((k - 64) <<< 8) + first) - 128) >>> 31 =
      if (k.toNat - 64) * 256 + first.toNat < 128 then 1 else 0 := by
    have h := bounded_sub_sign (c := 128) (((k - 64) <<< 8) + first) (by rw [ht]; omega) (by decide)
    rw [ht] at h
    exact h
  have low : (first - 1) >>> 31 = if first.toNat < 1 then 1 else 0 :=
    bounded_sub_sign first (c := 1) (by omega) (by decide)
  rw [low, top]
  have hpword : last &&& (1 : BitVec 32) = BitVec.ofNat 32 (last.toNat % 2) := parity_word last
  rw [hpword]
  have parity : last.toNat % 2 = 0 ∨ last.toNat % 2 = 1 := by omega
  rcases parity with hp | hp <;> rw [hp] <;>
    by_cases h1 : first.toNat < 1 <;>
    by_cases h2 : (k.toNat - 64) * 256 + first.toNat < 128 <;>
    simp only [h1, h2, ite_true, ite_false, decide_true, decide_false] <;> rfl

end VG.Proof.Bignum
