module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.RsaKeyGen.Gcd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: comparisons and selections on words

Without the carry bit, `ltU d a b` compares two 64-bit numbers by their
top bits and the borrow of their low 63 bits (`ltU_val`); a mask `0 − f` of
a flag `f ∈ {0, 1}` selects between two words by `y ^ ((x ^ y) & mask)`
(`sel_mask`). `gcdStep_ok`: one step of the binary gcd, as
`Proof.RsaKeyGen.gcdStep`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.RsaKeyGen.PPC64LE.Candidate

/-! ## Values -/

theorem shr63_val (a : BitVec 64) : a >>> 63 = BitVec.ofNat 64 (a.toNat / 2 ^ 63) := by
  have := a.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem low63_val (a : BitVec 64) : a <<< 1 >>> 1 = BitVec.ofNat 64 (a.toNat % 2 ^ 63) := by
  have := a.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show a.toNat % 2 ^ 63 < 2 ^ 64 by omega)]
  omega

theorem borrow63_val {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = BitVec.ofNat 64 (if x < y then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> omega

/-- `ltU`'s value: 1 if `a < b`, else 0. -/
theorem ltU_val (a b : BitVec 64) :
    (a >>> 63 ^^^ b >>> 63 ^^^ BitVec.ofNat 64 1) &&& (a <<< 1 >>> 1 - b <<< 1 >>> 1) >>> 63 |||
        b >>> 63 &&& (a >>> 63 ^^^ b >>> 63) = BitVec.ofNat 64 (if a.toNat < b.toNat then 1 else 0) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [shr63_val a, shr63_val b, low63_val a, low63_val b, borrow63_val (by omega) (by omega)]
  have hA : a.toNat / 2 ^ 63 = 0 ∨ a.toNat / 2 ^ 63 = 1 := by omega
  have hB : b.toNat / 2 ^ 63 = 0 ∨ b.toNat / 2 ^ 63 = 1 := by omega
  by_cases hl : a.toNat % 2 ^ 63 < b.toNat % 2 ^ 63
  · rw [ite_eq_left hl]
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB]
    · rw [ite_eq_left (by omega)]; decide
    · rw [ite_eq_left (by omega)]; decide
    · rw [ite_eq_right (by omega)]; decide
    · rw [ite_eq_left (by omega)]; decide
  · rw [ite_eq_right hl]
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB]
    · rw [ite_eq_right (by omega)]; decide
    · rw [ite_eq_left (by omega)]; decide
    · rw [ite_eq_right (by omega)]; decide
    · rw [ite_eq_right (by omega)]; decide

/-- A selection under the mask of a flag. -/
theorem sel_mask (c : Prop) [Decidable c] (x y : BitVec 64) :
    y ^^^ ((x ^^^ y) &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0))) = if c then x else y := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h, show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_comm y x, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  · rw [ite_eq_right h, ite_eq_right h, show BitVec.ofNat 64 0 - BitVec.ofNat 64 0 = 0#64 by decide, BitVec.and_zero,
      BitVec.xor_zero]

/-- The same, the other way round. -/
theorem sel_mask' (c : Prop) [Decidable c] (x y : BitVec 64) :
    (x ^^^ y) &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0)) ^^^ y = if c then x else y := by
  rw [BitVec.xor_comm, sel_mask]

/-- The low bit of a word as a flag. -/
theorem and1_val (a : BitVec 64) : a &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (if a.toNat % 2 = 1 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_comm, Nat.one_and_eq_mod_two]
  split <;> simp_all

end VG.Proof.RsaKeyGen.PPC64LE.Cand

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.RsaKeyGen.PPC64LE.Candidate

theorem gcdStep_ok {s : State} {u v : Nat} (h3 : s.gpr .r3 = BitVec.ofNat 64 u) (h21 : s.gpr .r21 = BitVec.ofNat 64 v)
    (hu : u < 2 ^ 64) (hv : v < 2 ^ 64) (hodd : v % 2 = 1) :
    WP isa (.block VG.Impl.RsaKeyGen.PPC64LE.Candidate.gcdStep) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdStep u v).1 ∧
        t.gpr .r21 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdStep u v).2 ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r15, .r16, .r21] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.gcdStep, ltU]
  prun [h3, h21, ltU_val, sel_mask, sel_mask', and1_val]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv]
  unfold VG.Proof.RsaKeyGen.gcdStep
  by_cases ho : u % 2 = 1
  · rw [ite_eq_left ho, ite_eq_left ho, ite_eq_left ho]
    by_cases hl : u < v
    · rw [ite_eq_left hl, ite_eq_left hl, ite_eq_left hl]
      refine ⟨BitVec.eq_of_toNat_eq ?_, rfl⟩
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      omega
    · rw [ite_eq_right hl, ite_eq_right hl, ite_eq_right hl]
      refine ⟨BitVec.eq_of_toNat_eq ?_, rfl⟩
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      omega
  · rw [ite_eq_right ho, ite_eq_right ho, ite_eq_right ho]
    refine ⟨BitVec.eq_of_toNat_eq ?_, rfl⟩
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega


/-- The condition of `modBit`'s subtraction. -/
theorem flag_val (p : Prop) [Decidable p] (a : BitVec 64) :
    BitVec.ofNat 64 (if p then 1 else 0) ^^^ BitVec.ofNat 64 1 ||| a >>> 63 =
      BitVec.ofNat 64 (if ¬p ∨ 2 ^ 63 ≤ a.toNat then 1 else 0) := by
  rw [shr63_val]
  have := a.isLt
  by_cases hp : p
  · by_cases ha : 2 ^ 63 ≤ a.toNat
    · rw [ite_eq_left hp, ite_eq_left (Or.inr ha), show a.toNat / 2 ^ 63 = 1 by omega]; decide
    · rw [ite_eq_left hp, ite_eq_right (fun h => h.elim (· hp) ha), show a.toNat / 2 ^ 63 = 0 by omega]; decide
  · rw [ite_eq_right hp, ite_eq_left (Or.inl hp)]
    have : a.toNat / 2 ^ 63 = 0 ∨ a.toNat / 2 ^ 63 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> decide

/-- `modBit`: `r3 := (2 r3 + x₆₃) mod e` for `r3 < e`, and `r7 := 2 x`. -/
theorem modBit_ok {s : State} {acc x e : Nat} (h3 : s.gpr .r3 = BitVec.ofNat 64 acc)
    (h7 : s.gpr .r7 = BitVec.ofNat 64 x) (h21 : s.gpr .r21 = BitVec.ofNat 64 e) (hacc : acc < e)
    (he : e < 2 ^ 64) (hx : x < 2 ^ 64) :
    WP isa (.block modBit) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 ((2 * acc + x / 2 ^ 63) % e) ∧ t.gpr .r7 = BitVec.ofNat 64 (2 * x % 2 ^ 64) ∧
        t.gpr .r21 = s.gpr .r21 ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4, .r7, .r8, .r9, .r15, .r16] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [modBit, ltU]
  prun [h3, h7, h21, ltU_val, flag_val, sel_mask]
  simp only [show (9223372036854775808 : Nat) = 2 ^ 63 by decide, show (18446744073709551616 : Nat) = 2 ^ 64 by decide]
  have hb : x / 2 ^ 63 ≤ 1 := by omega
  have hy : BitVec.ofNat 64 acc <<< 1 + BitVec.ofNat 64 x >>> 63 =
      BitVec.ofNat 64 (2 * acc % 2 ^ 64 + x / 2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hx]
    omega
  refine ⟨?_, ?_⟩
  · rw [hy, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he,
      Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega)]
    by_cases hA : 2 ^ 63 ≤ acc
    · rw [ite_eq_left (Or.inr hA)]
      have hm : (2 * acc + x / 2 ^ 63) % e = 2 * acc + x / 2 ^ 63 - e := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hm]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    · have hyl : (2 * acc % 2 ^ 64 + x / 2 ^ 63) % 2 ^ 64 = 2 * acc + x / 2 ^ 63 := by omega
      rw [hyl]
      by_cases hl : 2 * acc + x / 2 ^ 63 < e
      · rw [ite_eq_right (by omega), Nat.mod_eq_of_lt hl]
        exact congrArg _ (by omega)
      · rw [ite_eq_left (Or.inl hl)]
        have hm : (2 * acc + x / 2 ^ 63) % e = 2 * acc + x / 2 ^ 63 - e := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hm]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hx]
    omega

end VG.Proof.RsaKeyGen.PPC64LE.Cand
