module
public import VerifiedGarbage.Spec.RsaPss

import VerifiedGarbage.Proof.RsaPss.Arm.CtXor
import VerifiedGarbage.Proof.RsaPss.Params
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPss.Arm.Step
public import VerifiedGarbage.Proof.RsaPss.Arm.Base
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS on ARMv7: the encoding's parameters

From the modulus' first byte `n₀` (`x`), `params` stores the mask `c` of
`maskedDB`'s first byte (`cW`), `lo` (`loW`) and `dbLen = k - lo - hLen - 1`
(`dbW`) to their slots, and `saltFits` (after `expLen` when verifying) sets
the flags of whether everything fits (`fits_z`): `n₀ ≠ 0` and
`lo + hLen + 2 + sLen ≤ k`. The values, from a table of the 256 bytes
(`params_table`), are the specification's (`cW_byte`, `lo_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (dpVal)

/-- `2^⌊log₂ x⌋ - 1` for `x ≥ 2`, as `params` computes it. -/
abbrev smearW (x : BitVec 32) : BitVec 32 :=
  x >>> 1 ||| x >>> 1 >>> 1 ||| (x >>> 1 ||| x >>> 1 >>> 1) >>> 2 |||
    (x >>> 1 ||| x >>> 1 >>> 1 ||| (x >>> 1 ||| x >>> 1 >>> 1) >>> 2) >>> 4

/-- `lo`: 1 if `x ≤ 1`. -/
abbrev loW (x : BitVec 32) : BitVec 32 := (smearW x - 1) >>> 31

/-- The mask of `maskedDB`'s first byte. -/
abbrev cW (x : BitVec 32) : BitVec 32 := smearW x ||| (0 - loW x) &&& 0xFF

/-- `dbLen = k - lo - hLen - 1`. -/
abbrev dbW (K D : Nat) (x : BitVec 32) : BitVec 32 := BitVec.ofNat 32 K - loW x - BitVec.ofNat 32 (D + 1)

theorem params_table : ∀ x < 256, loW (BitVec.ofNat 32 x) = (if x ≤ 1 then 1 else 0) ∧
    (x = 1 → cW (BitVec.ofNat 32 x) = 0xFF) ∧
    (2 ≤ x → ∃ j < 8, 2 ^ j ≤ x ∧ x < 2 ^ (j + 1) ∧ cW (BitVec.ofNat 32 x) = BitVec.ofNat 32 (2 ^ j - 1)) := by
  decide +kernel

theorem setWidth_byte (b : Byte) : b.setWidth 32 = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- `lo` of a byte. -/
theorem loW_byte (b : Byte) : loW (b.setWidth 32) = BitVec.ofNat 32 (if b.toNat ≤ 1 then 1 else 0) := by
  rw [setWidth_byte, (params_table b.toNat b.isLt).1]
  split <;> rfl

theorem dbW_byte (K D : Nat) (b : Byte) :
    dbW K D (b.setWidth 32) = BitVec.ofNat 32 K - BitVec.ofNat 32 (if b.toNat ≤ 1 then 1 else 0) -
      BitVec.ofNat 32 (D + 1) := by
  show BitVec.ofNat 32 K - loW (b.setWidth 32) - _ = _
  rw [loW_byte]

/-- The mask of a byte not zero: the specification's `0xFF >>> z`. -/
theorem cW_byte {b : Byte} (h0 : b ≠ 0) (rest : List Byte) :
    (cW (b.setWidth 32)).setWidth 8 =
      (0xFF : Byte) >>> (8 * Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) -
        (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1)) := by
  rw [RsaPss.mask_eq rest h0, setWidth_byte]
  have hb := b.isLt
  have hn : b.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  obtain ⟨-, h1, h2⟩ := params_table b.toNat hb
  by_cases e : b.toNat = 1
  · rw [h1 e, ite_eq_left e]; rfl
  · obtain ⟨j, hj, hl, hu, he⟩ := h2 (by omega)
    rw [he, ite_eq_right e, RsaPss.log2_eq hn hl hu]
    apply BitVec.eq_of_toNat_eq
    have : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-- `lo = k - emLen`, for a first byte not zero. -/
theorem lo_eq {b : Byte} (h0 : b ≠ 0) (rest : List Byte) :
    (b :: rest).length - Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) =
      if b.toNat ≤ 1 then 1 else 0 := by
  rw [RsaPss.emLength_eq rest h0, List.length_cons]
  have hn : b.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  by_cases e : b.toNat = 1
  · rw [ite_eq_left e, ite_eq_left (by omega)]; omega
  · rw [ite_eq_right e, ite_eq_right (by omega)]; omega

/-- Whether a word is not zero, as the top bit of `-x | x`. -/
theorem nzW (x : BitVec 32) : ((0 - x) ||| x) >>> 31 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · rw [ite_eq_right h]
    apply BitVec.eq_of_toNat_eq
    have hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_or, BitVec.toNat_sub]
    show (((2 ^ 32 - x.toNat + 0) % 2 ^ 32) ||| x.toNat) / 2 ^ 31 = 1
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    by_cases hb : x.toNat < 2 ^ 31
    · have : 2 ^ 31 ≤ (2 ^ 32 - x.toNat) ||| x.toNat := Nat.le_trans (by omega) Nat.left_le_or
      have : (2 ^ 32 - x.toNat) ||| x.toNat < 2 ^ 32 := Nat.or_lt_two_pow (by omega) hlt
      omega
    · have : 2 ^ 31 ≤ (2 ^ 32 - x.toNat) ||| x.toNat := Nat.le_trans (by omega) Nat.right_le_or
      have : (2 ^ 32 - x.toNat) ||| x.toNat < 2 ^ 32 := Nat.or_lt_two_pow (by omega) hlt
      omega

/-- The flags of `saltFits`: whether everything fits. -/
theorem fits_z {x K D sl lo : Nat} (hx : x < 256) (hK : K ≤ 1024) (hD : D ≤ 64) (hsl : sl < 2 ^ 32) (hlo : lo ≤ 1) :
    (((BitVec.ofNat 32 x - 1) >>> 31 |||
        (BitVec.ofNat 32 K - BitVec.ofNat 32 lo - BitVec.ofNat 32 (D + 1) - 1) >>> 31 |||
        (BitVec.ofNat 32 K - BitVec.ofNat 32 lo - BitVec.ofNat 32 (D + 1) - 1 - BitVec.ofNat 32 sl) >>> 31 |||
        BitVec.ofNat 32 sl >>> 31) - 0 == 0) = decide (x ≠ 0 ∧ lo + D + 2 + sl ≤ K) := by
  have e1 : (BitVec.ofNat 32 x - 1) >>> 31 = if x < 1 then 1 else 0 := ltBit (b := 1) (by omega) (by decide)
  have e2 : BitVec.ofNat 32 K - BitVec.ofNat 32 lo - BitVec.ofNat 32 (D + 1) - 1 =
      BitVec.ofNat 32 K - BitVec.ofNat 32 (lo + D + 2) := by
    rw [BitVec.sub_sub, BitVec.sub_sub, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat,
      BitVec.ofNat_add_ofNat, show lo + (D + 1 + 1) = lo + D + 2 by omega]
  have e3 : BitVec.ofNat 32 sl >>> 31 = if 2 ^ 31 ≤ sl then 1 else 0 := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr hsl]
    by_cases h : 2 ^ 31 ≤ sl
    · rw [ite_eq_left h, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; rfl
    · rw [ite_eq_right h, Nat.div_eq_of_lt (by omega)]; rfl
  have hz : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
  have hor : ∀ a b : BitVec 32, (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := fun a b => BitVec.or_eq_zero_iff
  have hb01 : ∀ (p : Prop) [Decidable p], ((if p then (1 : BitVec 32) else 0) = 0) ↔ ¬ p := by
    intro p _; by_cases hp : p <;> simp [hp]
  rw [e1, e2, ltBit (by omega) (by omega), e3, hz, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, hor, hor, hor,
    hb01, hb01, hb01]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have hf : lo + D + 2 ≤ K := by omega
    rw [Offset.ofNat_sub_ofNat hf, ltBit (by omega) (by omega), hb01] at h3
    omega
  · rintro ⟨h1, h2⟩
    have hf : lo + D + 2 ≤ K := by omega
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    rw [Offset.ofNat_sub_ofNat hf, ltBit (by omega) (by omega), hb01]
    omega

variable {L : Lay} {scr : BitVec 32}

/-- `params`, from the modulus at `r0` (its first byte `x`), `k` in `r1` and
`hLen + 1` in `r11`, with `r12 = sp`. -/
theorem params_wp (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) {nP : BitVec 32} {K D : Nat}
    (r0 : s.gpr .r0 = nP) (hn : InRegions (s.rd ++ s.wr) (State.addr nP) 1) (r1 : s.gpr .r1 = BitVec.ofNat 32 K)
    (r11 : s.gpr .r11 = BitVec.ofNat 32 (D + 1)) (r12 : s.gpr .r12 = L.B) :
    WP isa (.block params) s fun t =>
      t.mem = ((s.mem.writeW (L.fr sC) (cW ((s.mem (State.addr nP)).setWidth 32))).writeW (L.fr sLo)
        (loW ((s.mem (State.addr nP)).setWidth 32))).writeW (L.fr sDb) (dbW K D ((s.mem (State.addr nP)).setWidth 32)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r8 = ((s.mem (State.addr nP)).setWidth 32 - 1) >>> 31 |||
        (dbW K D ((s.mem (State.addr nP)).setWidth 32) - 1) >>> 31 ∧
      t.gpr .r9 = dbW K D ((s.mem (State.addr nP)).setWidth 32) - 1 ∧
      t.gpr .r2 = s.gpr .r2 ∧ t.gpr .r10 = s.gpr .r10 ∧ t.gpr .r12 = s.gpr .r12 := by
  prun [params, st, mw, r0, r1, r11, r12, hn, hc.aFr hg, hc.wFr hg, dpVal, smearW, loW, cW, dbW]

/-- `saltFits`: the flags of whether the salt length `r2` also fits. -/
theorem saltFits_wp (s : State) :
    WP isa (.block saltFits) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.z = ((s.gpr .r8 ||| (s.gpr .r9 - s.gpr .r2) >>> 31 ||| s.gpr .r2 >>> 31) - 0 == 0) := by
  prun [saltFits, dpVal]

/-- `expLen`: `[any_salt_len ≠ 0]` (from `r10`) to its slot, and the
expected salt length in `r2`, 0 if any. -/
theorem expLen_wp (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) (r12 : s.gpr .r12 = L.B) :
    WP isa (.block expLen) s fun t =>
      t.mem = s.mem.writeW (L.fr sAny) (if s.gpr .r10 = 0 then (0 : BitVec 32) else 1) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r2 = (if s.gpr .r10 = 0 then s.gpr .r2 else 0) ∧ t.gpr .r8 = s.gpr .r8 ∧
      t.gpr .r9 = s.gpr .r9 := by
  have e : ∀ x : BitVec 32, (0 - x ||| x) >>> 31 = if x = 0 then 0 else 1 := nzW
  prun [expLen, st, mw, r12, hc.aFr hg, hc.wFr hg, dpVal, e]
  by_cases h0 : s.gpr .r10 = 0
  · simp only [h0, ite_true]
    rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
  · simp only [h0, ite_false]
    rw [show (1 : BitVec 32) - 1 = 0 by decide]
    exact BitVec.and_zero

end VG.Proof.RsaPss.Arm
