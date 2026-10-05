import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.RsaPss.MgfBytes

/-!
# RSASSA-PSS: the encoding's parameters from the modulus' first octet

For a modulus `n₀ ‖ rest` with `n₀ ≠ 0`, `emBits = 8 |rest| + ⌊log₂ n₀⌋`
(`emBits_eq`), so `emLen = |rest|` if `n₀ = 1` and `|rest| + 1` otherwise
(`emLength_eq`), and `0xFF >>> (8 emLen - emBits)` is `0xFF` if `n₀ = 1`
and `2^⌊log₂ n₀⌋ - 1` otherwise (`mask_eq`): what the implementations
compute from `n₀` alone.
-/

namespace VG.Proof.RsaPss

open VG.Spec
open VG.Spec.RsaPss (bitLength emLength)

theorem os2ip_foldl' (a : Nat) (bs : List Byte) :
    bs.foldl (fun x b => 256 * x + b.toNat) a = a * 256 ^ bs.length + Rsa.os2ip bs := by
  induction bs generalizing a with
  | nil => simp [Rsa.os2ip]
  | cons b bs ih =>
    show bs.foldl _ (256 * a + b.toNat) = a * 256 ^ (bs.length + 1) + bs.foldl _ (256 * 0 + b.toNat)
    rw [ih, ih (256 * 0 + b.toNat), Nat.pow_succ, Nat.add_mul, Nat.mul_zero, Nat.zero_add, Nat.mul_assoc,
      Nat.mul_comm (256 ^ bs.length) 256, Nat.add_assoc, Nat.mul_left_comm]

theorem os2ip_cons' (b : Byte) (bs : List Byte) :
    Rsa.os2ip (b :: bs) = b.toNat * 256 ^ bs.length + Rsa.os2ip bs := by
  show List.foldl (fun x (b : Byte) => 256 * x + b.toNat) (256 * 0 + b.toNat) bs = _
  rw [os2ip_foldl', Nat.mul_zero, Nat.zero_add]

theorem os2ip_lt' : ∀ bs : List Byte, Rsa.os2ip bs < 256 ^ bs.length
  | [] => by decide
  | b :: bs => by
    rw [os2ip_cons', List.length_cons, Nat.pow_succ]
    have := os2ip_lt' bs
    have hb := b.isLt
    have : b.toNat * 256 ^ bs.length + 256 ^ bs.length ≤ 256 ^ bs.length * 256 := by
      rw [← Nat.succ_mul, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega

/-- The bits of the integer below the top octet. -/
theorem log2_eq {x m : Nat} (hx : x ≠ 0) (h1 : 2 ^ m ≤ x) (h2 : x < 2 ^ (m + 1)) : Nat.log2 x = m :=
  Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.log2_lt hx).mpr h2)) ((Nat.le_log2 hx).mpr h1)

theorem emBits_eq {n₀ : Byte} (rest : List Byte) (h0 : n₀ ≠ 0) :
    bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = 8 * rest.length + Nat.log2 n₀.toNat := by
  have hn : n₀.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have hl := (Nat.le_log2 hn).mp (Nat.le_refl _)
  have hu := (Nat.log2_lt hn).mp (Nat.lt_succ_self _)
  have hr := os2ip_lt' rest
  have hP : (256 : Nat) ^ rest.length = 2 ^ (8 * rest.length) := by rw [Nat.pow_mul]
  unfold bitLength
  rw [os2ip_cons', Nat.add_sub_cancel]
  have hpos : 0 < 256 ^ rest.length := Nat.pow_pos (by decide)
  have hm := Nat.mul_le_mul_right (256 ^ rest.length) (Nat.one_le_iff_ne_zero.mpr hn)
  refine log2_eq (by omega) ?_ ?_
  · rw [Nat.pow_add, hP, Nat.mul_comm]
    exact Nat.le_add_right_of_le (Nat.mul_le_mul_right _ hl)
  · rw [hP] at hr ⊢
    rw [show 8 * rest.length + Nat.log2 n₀.toNat + 1 = (Nat.log2 n₀.toNat + 1) + 8 * rest.length by omega,
      Nat.pow_add]
    have : (n₀.toNat + 1) * 2 ^ (8 * rest.length) ≤ 2 ^ (Nat.log2 n₀.toNat + 1) * 2 ^ (8 * rest.length) :=
      Nat.mul_le_mul_right _ hu
    rw [Nat.succ_mul] at this; omega

theorem log2_lt8 (x : Byte) : Nat.log2 x.toNat < 8 := by
  by_cases h : x.toNat = 0
  · rw [h]; decide
  · exact (Nat.log2_lt h).mpr x.isLt

theorem log2_eq_zero {x : Byte} (h : x.toNat ≠ 0) : Nat.log2 x.toNat = 0 ↔ x.toNat = 1 := by
  constructor
  · intro h'
    have := (Nat.log2_lt h).mp (show Nat.log2 x.toNat < 1 by omega)
    omega
  · intro h'; rw [h']; decide

theorem emLength_eq {n₀ : Byte} (rest : List Byte) (h0 : n₀ ≠ 0) :
    emLength (bitLength (Rsa.os2ip (n₀ :: rest)) - 1) = rest.length + if n₀.toNat = 1 then 0 else 1 := by
  have hn : n₀.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  rw [emBits_eq rest h0, emLength]
  have h8 := log2_lt8 n₀
  have hz := log2_eq_zero hn
  split
  · rw [hz.mpr (by assumption)]; omega
  · have : Nat.log2 n₀.toNat ≠ 0 := fun h => by simp_all
    omega

/-- `0xFF >>> z`, where `z = 8 emLen - emBits`. -/
theorem mask_eq {n₀ : Byte} (rest : List Byte) (h0 : n₀ ≠ 0) :
    (0xFF : Byte) >>> (8 * emLength (bitLength (Rsa.os2ip (n₀ :: rest)) - 1) -
      (bitLength (Rsa.os2ip (n₀ :: rest)) - 1)) =
      if n₀.toNat = 1 then 0xFF else BitVec.ofNat 8 (2 ^ Nat.log2 n₀.toNat - 1) := by
  have hn : n₀.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  rw [emLength_eq rest h0, emBits_eq rest h0]
  have h8 := log2_lt8 n₀
  have hz := log2_eq_zero hn
  split
  · rw [hz.mpr (by assumption)]
    rw [show 8 * (rest.length + 0) - (8 * rest.length + 0) = 0 by omega]; rfl
  · have : Nat.log2 n₀.toNat ≠ 0 := fun h => by simp_all
    rw [show 8 * (rest.length + 1) - (8 * rest.length + Nat.log2 n₀.toNat) = 8 - Nat.log2 n₀.toNat by omega]
    generalize Nat.log2 n₀.toNat = j at h8 this
    revert j; decide

end VG.Proof.RsaPss
