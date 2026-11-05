module

public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.Words

-- separate module: target-independent, for each target's verification of the hash function's output

/-!
# ECDSA verification of the hash function's output: the hash's `len` bytes

Untrusted: everything here is checked by Lean. `vg_ecdsa_<curve>_verify`
takes the hash as the hash function's output (`Instance.verifyHashContract`);
on each target it writes `fixedDigest` of it, `len` bytes, to a buffer, and
runs the verification that takes those `len` bytes (`Proof.Ecdsa.verifyContract`)
on them. `fixedDigest` is the hash's leftmost `len` bytes, or, for a shorter
hash, the hash after zero bytes, shifted left by a further 7 bits (`shr1` of
the hash after a zero byte) for a curve whose `n` has 7 bits fewer than `8 len`
(`wide`, P-521). Either way its integer `e` is the hash's
(`hashToInt_fixedDigest`), so the two verifications agree.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify

open VG VG.Proof.Weierstrass VG.Proof.Ecdsa.Rfc6979

/-- The byte of the bits 1–8 of the pair `a b`: `a`'s low bit, then `b`'s
seven high bits. -/
def sh (a b : Byte) : Byte := BitVec.ofNat 8 (a.toNat % 2 * 128 + b.toNat / 2)

/-- The bytes shifted right by one bit, without their last byte: byte `i`
is `sh` of bytes `i` and `i + 1`. -/
def shr1 : List Byte → List Byte
  | a :: b :: r => sh a b :: shr1 (b :: r)
  | _ => []

/-- The `len` bytes whose integer `e` is the hash `H`'s, on a curve whose
`n` has `8 len` bits, or, if `wide`, `8 len - 7`. -/
def fixedDigest (len : Nat) (wide : Bool) (H : List Byte) : List Byte :=
  if len ≤ H.length then H.take len
  else if wide then shr1 (List.replicate (len - H.length) 0 ++ H ++ [0])
  else List.replicate (len - H.length) 0 ++ H

theorem sh_toNat (a b : Byte) : (sh a b).toNat = a.toNat % 2 * 128 + b.toNat / 2 := by
  have hb := b.isLt
  rw [sh, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem length_shr1 : ∀ (a : Byte) (r : List Byte), (shr1 (a :: r)).length = r.length
  | _, [] => rfl
  | a, b :: r => by rw [shr1, List.length_cons, length_shr1 b r, List.length_cons]

theorem ofBytes_cons (b : Byte) (r : List Byte) :
    Spec.Weierstrass.ofBytes (b :: r) = b.toNat * 2 ^ (8 * r.length) + Spec.Weierstrass.ofBytes r := by
  rw [show b :: r = [b] ++ r from rfl, ofBytes_append, ofBytes_single, pow256]

/-- Halving `a P + X` (`X < 2 P`, `P` the place value of `a`'s next byte),
modulo `2 P`... in the form `ofBytes_shr1` needs. -/
theorem half_step (a b P Y Z : Nat) (_ha : a < 256) (hb : b < 256) (hY : Y < P)
    (hZ : Z = (b % 2 * P + Y) / 2) :
    (a % 2 * 128 + b / 2) * P + (b * P + Y) / 2 % P = (a * (256 * P) + (b * P + Y)) / 2 % (256 * P) := by
  have hbP : b % 2 * P ≤ P := by
    have : b % 2 ≤ 1 := by omega
    calc b % 2 * P ≤ 1 * P := Nat.mul_le_mul_right _ this
      _ = P := Nat.one_mul P
  have hZP : Z < P := by omega
  have e1 : b * P + Y = (b % 2 * P + Y) + (b / 2 * P) * 2 := by
    conv => lhs; rw [← Nat.div_add_mod b 2]
    grind
  have e2 : (b * P + Y) / 2 = Z + b / 2 * P := by
    rw [e1, Nat.add_mul_div_right _ _ (by decide), hZ]
  have e3 : (b * P + Y) / 2 % P = Z := by
    rw [e2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hZP]
  have e4 : a * (256 * P) + (b * P + Y) =
      (b % 2 * P + Y + ((a % 2 * 128 + b / 2) * P + a / 2 * (256 * P)) * 2) := by
    rw [e1]
    conv => lhs; rw [← Nat.div_add_mod a 2]
    grind
  rw [e3, e4, Nat.add_mul_div_right _ _ (by decide), ← hZ, ← Nat.add_assoc, Nat.add_comm Z,
    Nat.add_mul_mod_self_right]
  refine (Nat.mod_eq_of_lt ?_).symm
  have hs : a % 2 * 128 + b / 2 + 1 ≤ 256 := by omega
  calc (a % 2 * 128 + b / 2) * P + Z < (a % 2 * 128 + b / 2) * P + P := by omega
    _ = (a % 2 * 128 + b / 2 + 1) * P := by rw [Nat.succ_mul]
    _ ≤ 256 * P := Nat.mul_le_mul_right _ hs

/-- `shr1` halves the number, but for its leading byte's bits. -/
theorem ofBytes_shr1 : ∀ (a : Byte) (r : List Byte),
    Spec.Weierstrass.ofBytes (shr1 (a :: r)) = Spec.Weierstrass.ofBytes (a :: r) / 2 % 2 ^ (8 * r.length)
  | _, [] => by simp [shr1, Spec.Weierstrass.ofBytes, Nat.mod_one]
  | a, b :: r => by
    rw [shr1, ofBytes_cons, length_shr1, ofBytes_shr1 b r, sh_toNat, ofBytes_cons a,
      ofBytes_cons b, List.length_cons]
    have hY := ofBytes_lt r
    have hP' : 2 ^ (8 * (r.length + 1)) = 256 * 2 ^ (8 * r.length) := by
      rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
    rw [hP']
    exact half_step _ _ _ _ _ a.isLt b.isLt hY rfl

theorem ofBytes_replicate_zero (k : Nat) (l : List Byte) :
    Spec.Weierstrass.ofBytes (List.replicate k 0 ++ l) = Spec.Weierstrass.ofBytes l := ofBytes_zeros k l

/-- The integer `e` of `fixedDigest` is the hash's, on a curve whose `n` has
`8 len` bits, or `8 len - 7` if `wide`. -/
theorem hashToInt_fixedDigest {C : Spec.Weierstrass.Curve} {len : Nat} {wide : Bool}
    (hL : 8 * len = Spec.Ecdsa.nBits C + if wide then 7 else 0) (H : List Byte) :
    Spec.Ecdsa.hashToInt C (fixedDigest len wide H) = Spec.Ecdsa.hashToInt C H := by
  have h₁ : Spec.Ecdsa.nBits C ≤ 8 * len := by split at hL <;> omega
  unfold fixedDigest
  by_cases hl : len ≤ H.length
  · simp only [hl, ite_true]
    rw [hashToInt_takeR h₁ (by rw [List.length_take]; omega), List.take_take, Nat.min_self,
      hashToInt_takeR h₁ hl]
  · simp only [hl, ite_false]
    have hs : Spec.Ecdsa.hashToInt C H = Spec.Weierstrass.ofBytes H := by
      rw [Spec.Ecdsa.hashToInt]
      simp only [show 8 * H.length ≤ Spec.Ecdsa.nBits C by split at hL <;> omega, ite_true]
    rw [hs]
    have hH := ofBytes_lt H
    cases wide with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hL ⊢
      rw [Spec.Ecdsa.hashToInt]
      simp only [List.length_append, List.length_replicate,
        show 8 * (len - H.length + H.length) ≤ Spec.Ecdsa.nBits C by omega, ite_true]
      exact ofBytes_replicate_zero _ _
    | true =>
      simp only [ite_true] at hL ⊢
      have hT : List.replicate (len - H.length) (0 : Byte) ++ H ++ [0] =
          (0 : Byte) :: (List.replicate (len - H.length - 1) 0 ++ H ++ [0]) := by
        rw [show len - H.length = (len - H.length - 1) + 1 by omega, List.replicate_succ]
        simp
      have hlen : (List.replicate (len - H.length - 1) (0 : Byte) ++ H ++ [0]).length = len := by
        simp only [List.length_append, List.length_replicate, List.length_singleton]; omega
      have hB : (shr1 ((0 : Byte) :: (List.replicate (len - H.length - 1) 0 ++ H ++ [0]))).length = len := by
        rw [length_shr1, hlen]
      have hv : Spec.Weierstrass.ofBytes (shr1 ((0 : Byte) :: (List.replicate (len - H.length - 1) 0 ++ H ++ [0]))) =
          Spec.Weierstrass.ofBytes H * 128 := by
        rw [ofBytes_shr1, hlen, ofBytes_cons, hlen, List.append_assoc, ofBytes_replicate_zero,
          ofBytes_append, List.length_singleton, ofBytes_single]
        rw [show (0 : Byte).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.pow_one,
          show Spec.Weierstrass.ofBytes H * 256 = Spec.Weierstrass.ofBytes H * 128 * 2 by omega,
          Nat.mul_div_cancel _ (by decide : 0 < 2)]
        refine Nat.mod_eq_of_lt ?_
        have : 2 ^ (8 * H.length) * 128 ≤ 2 ^ (8 * len) := by
          rw [show 8 * len = 8 * H.length + 7 + (8 * (len - H.length) - 7) by omega, Nat.pow_add,
            Nat.pow_add]
          exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
        calc Spec.Weierstrass.ofBytes H * 128 < 2 ^ (8 * H.length) * 128 := Nat.mul_lt_mul_of_pos_right hH (by decide)
          _ ≤ _ := this
      rw [hT, Spec.Ecdsa.hashToInt, hB, hv]
      simp only [show ¬ 8 * len ≤ Spec.Ecdsa.nBits C by omega, ite_false]
      rw [show 8 * len - Spec.Ecdsa.nBits C = 7 by omega, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (by decide)]

/-! ## Bytes in memory -/

theorem bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) (hi : i < n) :
    (Spec.Ecdsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Ecdsa.bytesAt, hi]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Ecdsa.bytesAt m p n).length = n := by
  simp [Spec.Ecdsa.bytesAt]

theorem shr1_getD : ∀ (l : List Byte) (i : Nat), i + 1 < l.length →
    (shr1 l).getD i 0 = sh (l.getD i 0) (l.getD (i + 1) 0)
  | a :: b :: r, 0, _ => by simp [shr1]
  | a :: b :: r, i + 1, h => by
    rw [shr1, List.getD_cons_succ, shr1_getD (b :: r) i (by simpa using h)]
    simp
  | [_], _, h => by simp at h
  | [], _, h => by simp at h

/-- The value `shiftBytes` stores. -/
theorem shift_byte (b c : Byte) :
    ((b.setWidth 64 <<< 7) + (c.setWidth 64 >>> 1)).setWidth 8 = sh b c := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  have hc := c.isLt
  rw [sh_toNat, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  omega

/-- The bytes of the buffer after the zeros and the hash: the hash at
`len - d`. -/
def tz (len : Nat) (H : List Byte) (j : Nat) : Byte :=
  if len - H.length ≤ j ∧ j < len then H.getD (j - (len - H.length)) 0 else 0

theorem tz_getD {len : Nat} {H : List Byte} (hl : H.length < len) {j : Nat} (hj : j ≤ len) :
    (List.replicate (len - H.length) (0 : Byte) ++ H ++ [0]).getD j 0 = tz len H j := by
  unfold tz
  rw [List.append_assoc, List.getD_eq_getElem?_getD]
  by_cases h₁ : j < len - H.length
  · rw [List.getElem?_append_left (by simpa using h₁)]
    simp [h₁, show ¬ (len - H.length ≤ j) by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate]
    by_cases h₂ : j < len
    · rw [List.getElem?_append_left (by omega)]
      simp [show len - H.length ≤ j by omega, h₂, List.getD_eq_getElem?_getD]
    · have e : j - (len - H.length) - H.length = 0 := by omega
      rw [List.getElem?_append_right (by omega), e]
      simp [h₂]

theorem fixed_short {len : Nat} {H : List Byte} (hl : H.length < len) (wide : Bool) {i : Nat}
    (hi : i < len) :
    (fixedDigest len wide H).getD i 0 =
      if wide then sh (tz len H i) (tz len H (i + 1)) else tz len H i := by
  unfold fixedDigest
  simp only [show ¬ len ≤ H.length by omega, ite_false]
  cases wide with
  | true =>
    simp only [ite_true]
    rw [shr1_getD _ _ (by simp; omega), tz_getD hl (by omega), tz_getD hl (by omega)]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have := tz_getD hl (Nat.le_of_lt hi)
    rw [← this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (l₁ := List.replicate (len - H.length) 0 ++ H) (by simp; omega)]

theorem contains_sub {B x : Addr} {n k : Nat} (h : (⟨B, n⟩ : Region).Contains x 1) (hk : n ≤ k) :
    (⟨B, k⟩ : Region).Contains x 1 := by
  unfold Region.Contains at *; simp only at h ⊢; omega

theorem byte_writeW_ne' (m : Mem) (p : Addr) (b : Byte) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : j ≠ i) : (m.writeW (p + BitVec.ofNat 64 i) b) (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) := by
  rw [WriteBytes.writeW8_apply]
  simp only [Offset.add_ofNat_ne p hj hi h, ite_false]

theorem byte_writeW_eq (m : Mem) (p : Addr) (b : Byte) (i : Nat) :
    (m.writeW (p + BitVec.ofNat 64 i) b) (p + BitVec.ofNat 64 i) = b := by
  simp only [WriteBytes.writeW8_apply, ite_true]

theorem inRegions_wr {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem replicate_getD (n j : Nat) : (List.replicate n (0 : Nat)).getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

/-- The bytes `[off, off + n)` of the buffer are within its 80. -/
theorem in_buf {B x : Addr} {off n : Nat} (h : (⟨B + BitVec.ofNat 64 off, n⟩ : Region).Contains x 1)
    (hn : off + n ≤ 80) : (⟨B, 80⟩ : Region).Contains x 1 :=
  Offset.sub_base B hn x h

theorem nBits_pos (C : Spec.Weierstrass.Curve) : 0 < Spec.Ecdsa.nBits C := by
  unfold Spec.Ecdsa.nBits; omega

/-- The bytes of a region apart from the memory a frame changes. -/
theorem bytesAt_frame {R : Region} {m m' : Mem} (hf : Frame [R] m m') {p : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint R) (hn : n ≤ 2 ^ 64) :
    Spec.Ecdsa.bytesAt m' p n = Spec.Ecdsa.bytesAt m p n := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi : i < n := by simpa using hi
  exact Frame.bytes (R := ⟨p, n⟩) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)
    hn hi

theorem bytesAt_ext {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (hl : l.length = n)
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = l.getD i 0) : Spec.Ecdsa.bytesAt m p n = l := by
  refine List.ext_getElem (by rw [length_bytesAt, hl]) fun i h₁ h₂ => ?_
  have := h i (by rw [length_bytesAt] at h₁; exact h₁)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some] at this
  simp only [Spec.Ecdsa.bytesAt, List.getElem_map, List.getElem_range]
  exact this

theorem length_fixedDigest (len : Nat) (wide : Bool) (H : List Byte) : (fixedDigest len wide H).length = len := by
  unfold fixedDigest
  split
  · simp; omega
  · split
    · rw [show List.replicate (len - H.length) (0 : Byte) ++ H ++ [0] =
          (0 : Byte) :: (List.replicate (len - H.length - 1) 0 ++ H ++ [0]) by
        rw [show len - H.length = (len - H.length - 1) + 1 by omega, List.replicate_succ]; simp,
        length_shr1]
      simp; omega
    · simp; omega

theorem sub_prefix (B : Addr) {n k : Nat} (h : n ≤ k) : Region.Sub ⟨B, n⟩ ⟨B, k⟩ := fun x hx => by
  unfold Region.Contains at *; simp only at *; omega

theorem bytes_of_leak {a₁ b₁ c₁ a₂ b₂ c₂ : List Byte} (ha : a₁.length = a₂.length) (hb : b₁.length = b₂.length)
    (h : (a₁ ++ b₁ ++ c₁).map (·.toNat) = (a₂ ++ b₂ ++ c₂).map (·.toNat)) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  have e : a₁ ++ b₁ ++ c₁ = a₂ ++ b₂ ++ c₂ := by
    have := congrArg (List.map fun n => BitVec.ofNat 8 n) h
    simpa [List.map_map, Function.comp_def] using this
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [ha, hb])
  obtain ⟨e3, e4⟩ := List.append_inj e1 ha
  exact ⟨e3, e4, e2⟩

end VG.Proof.Ecdsa.Verify
