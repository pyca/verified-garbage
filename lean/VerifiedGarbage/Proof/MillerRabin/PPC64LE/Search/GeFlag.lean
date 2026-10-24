module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Omega

/-! # A prime search on PPC64LE: comparing numbers below `2^63` -/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Search

open VG VG.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.Bignum.PPC64LE

theorem ge_val {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 ^^^ BitVec.ofNat 64 1 ||| BitVec.ofNat 64 x >>> 63 =
      BitVec.ofNat 64 (if y ≤ x then 1 else 0) := by
  have e1 : BitVec.ofNat 64 x >>> 63 = BitVec.ofNat 64 (x / 2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)]
  by_cases hb : x < 2 ^ 63
  · have e : (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = BitVec.ofNat 64 (if y ≤ x then 0 else 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      split <;> omega
    rw [e, e1, Nat.div_eq_of_lt hb]; split <;> rfl
  · have e : (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 ^^^ BitVec.ofNat 64 1 =
        BitVec.ofNat 64 ((x - y) / 2 ^ 63 ^^^ 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_xor, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      have h1 : (2 ^ 64 - y % 2 ^ 64 + x % 2 ^ 64) % 2 ^ 64 = x - y := by omega
      rw [h1, Nat.mod_eq_of_lt (show (1 : Nat) < 2 ^ 64 by decide)]
      have : (x - y) / 2 ^ 63 ≤ 1 := by omega
      have : (x - y) / 2 ^ 63 ^^^ 1 ≤ 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> decide
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [e, e1, show x / 2 ^ 63 = 1 by omega, ite_eq_left (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : (x - y) / 2 ^ 63 ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> decide

/-- `geFlag r5 r3 r4`: `r5 := 1` if `r3 ≥ r4`, else 0. -/
theorem geFlag_ok {s : State} {x y : Nat} (h3 : s.gpr .r3 = BitVec.ofNat 64 x) (h4 : s.gpr .r4 = BitVec.ofNat 64 y)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 63) :
    WP isa (.block (geFlag .r5 .r3 .r4)) s fun t =>
      (t.gpr .r5 = BitVec.ofNat 64 (if y ≤ x then 1 else 0) ∧ t.mem = s.mem) ∧ Keep [.r5, .r0] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [geFlag]
  prun [h3, h4, ge_val hx hy]

end VG.Proof.MillerRabin.PPC64LE.Search
