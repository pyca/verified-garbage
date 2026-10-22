module

public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
public import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPss.Params
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: the encoding's parameters

From the modulus' first byte `n₀` (`x`), `params` stores `lo` (`loW`), the
mask `c` of `maskedDB`'s first byte (`cW`) and `dbLen = k - lo - hLen - 1`
(`dbW`) to their slots, and sets the flags of whether everything fits
(`fits_z`): `n₀ ≠ 0` and `lo + hLen + 2 + sLen ≤ k`. The values, from a
table of the 256 bytes (`params_table`), are the specification's (`cW_byte`,
`lo_eq`), as on ARMv7.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

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

/-- Nonzero if `n₀ = 0` or something does not fit. -/
abbrev failW (K D sl : Nat) (x : BitVec 32) : BitVec 32 :=
  (x - 1) >>> 31 ||| (dbW K D x - 1) >>> 31 ||| (dbW K D x - 1 - BitVec.ofNat 32 sl) >>> 31 |||
    BitVec.ofNat 32 sl >>> 31

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

/-- The top bit of a difference of numbers below `2^31`: whether the first
is less. -/
theorem ltBit {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b) >>> 31 = if a < b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega)]
  split
  · show _ = 1; omega
  · show _ = 0; omega

/-- The flags of `params`: whether everything fits. -/
theorem fits_z {x K D sl lo : Nat} (hx : x < 256) (hK : K ≤ 1024) (hD : D ≤ 64) (hsl : sl < 2 ^ 32)
    (hlo : lo ≤ 1) :
    ((BitVec.ofNat 32 x - 1) >>> 31 |||
        (BitVec.ofNat 32 K - BitVec.ofNat 32 lo - BitVec.ofNat 32 (D + 1) - 1) >>> 31 |||
        (BitVec.ofNat 32 K - BitVec.ofNat 32 lo - BitVec.ofNat 32 (D + 1) - 1 - BitVec.ofNat 32 sl) >>> 31 |||
        BitVec.ofNat 32 sl >>> 31 == 0) = decide (x ≠ 0 ∧ lo + D + 2 + sl ≤ K) := by
  have e1 : (BitVec.ofNat 32 x - 1) >>> 31 = if x < 1 then 1 else 0 := ltBit (b := 1) (by omega) (by decide)
  have e2 : BitVec.ofNat 32 K - BitVec.ofNat 32 lo - BitVec.ofNat 32 (D + 1) - 1 =
      BitVec.ofNat 32 K - BitVec.ofNat 32 (lo + D + 2) := by
    rw [BitVec.sub_sub, BitVec.sub_sub, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat,
      BitVec.ofNat_add_ofNat, show lo + (D + 1 + 1) = lo + D + 2 by omega]
  have e3 : BitVec.ofNat 32 sl >>> 31 = if 2 ^ 31 ≤ sl then 1 else 0 := by
    rw [ofNat_shr hsl]
    by_cases h : 2 ^ 31 ≤ sl
    · rw [ite_eq_left h, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; rfl
    · rw [ite_eq_right h, Nat.div_eq_of_lt (by omega)]; rfl
  have hor : ∀ a b : BitVec 32, (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := fun a b => BitVec.or_eq_zero_iff
  have hb01 : ∀ (p : Prop) [Decidable p], ((if p then (1 : BitVec 32) else 0) = 0) ↔ ¬ p := by
    intro p _; by_cases hp : p <;> simp [hp]
  rw [e1, e2, ltBit (by omega) (by omega), e3, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, hor, hor, hor,
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

/-- The flags of `params`, for the modulus' first byte `b`. -/
theorem failW_z {b : Byte} {K D sl : Nat} (hK : K ≤ 1024) (hD : D ≤ 64) (hsl : sl < 2 ^ 32) :
    (failW K D sl (b.setWidth 32) &&& failW K D sl (b.setWidth 32) == 0) =
      decide (b ≠ 0 ∧ (if b.toNat ≤ 1 then 1 else 0) + D + 2 + sl ≤ K) := by
  have hb : b ≠ 0 ↔ b.toNat ≠ 0 := ⟨fun h e => h (BitVec.eq_of_toNat_eq e), fun h e => h (by rw [e]; rfl)⟩
  rw [BitVec.and_self]
  show ((b.setWidth 32 - 1) >>> 31 ||| (BitVec.ofNat 32 K - loW (b.setWidth 32) - BitVec.ofNat 32 (D + 1) - 1) >>> 31 |||
    (BitVec.ofNat 32 K - loW (b.setWidth 32) - BitVec.ofNat 32 (D + 1) - 1 - BitVec.ofNat 32 sl) >>> 31 |||
      BitVec.ofNat 32 sl >>> 31 == 0) = _
  rw [loW_byte, setWidth_byte, fits_z b.isLt hK hD hsl (by split <;> omega)]
  simp only [hb]

/-- `params` from the modulus at `esi`, `k` in `ecx` and the salt length in
`edx`. -/
theorem params_wp (H : Impl.Pbkdf2.Md.X86.Hash) {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {σ s : State}
    (hc : Ctx L scr σ s) {nP : BitVec 32} {K sl : Nat}
    (esi : s.gpr .esi = nP) (hn : InRegions (s.rd ++ s.wr) (addr nP 0) 1) (ecx : s.gpr .ecx = BitVec.ofNat 32 K)
    (edx : s.gpr .edx = BitVec.ofNat 32 sl) :
    WP isa (.block (params H)) s fun t =>
      t.mem = ((s.mem.writeW (L.fr sLo) (loW ((s.mem (addr nP 0)).setWidth 32))).writeW (L.fr sC)
        (cW ((s.mem (addr nP 0)).setWidth 32))).writeW (L.fr sDb) (dbW K H.D ((s.mem (addr nP 0)).setWidth 32)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .esp = s.gpr .esp ∧ t.gpr .ebp = s.gpr .ebp ∧
      t.zf = some (failW K H.D sl ((s.mem (addr nP 0)).setWidth 32) &&&
        failW K H.D sl ((s.mem (addr nP 0)).setWidth 32) == 0) := by
  obtain ⟨σ', ok⟩ := hg.ok
  have w := hc.wFr hg
  psrun [params, st, mi, esi, ecx, edx, hn, hc.st.sp, w sLo (by decide), w sC (by decide), w sDb (by decide),
    hg.aFr ok sLo (by decide), hg.aFr ok sC (by decide), hg.aFr ok sDb (by decide)]
  rfl

end VG.Proof.RsaPss.X86
