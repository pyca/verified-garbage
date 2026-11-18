module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Witness
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Copy
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.Words
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-! ### `RsaKeyGen.PPC64LE.Cand.Gcd`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.Bits`, which this module and modules that import it used -/

section

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
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [])]

theorem low63_val (a : BitVec 64) : a <<< 1 >>> 1 = BitVec.ofNat 64 (a.toNat % 2 ^ 63) := by
  have := a.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show a.toNat % 2 ^ 63 < 2 ^ 64 by omega_using [])]
  omega_using []

theorem borrow63_val {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = BitVec.ofNat 64 (if x < y then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> omega_arith

/-- `ltU`'s value: 1 if `a < b`, else 0. -/
theorem ltU_val (a b : BitVec 64) :
    (a >>> 63 ^^^ b >>> 63 ^^^ BitVec.ofNat 64 1) &&& (a <<< 1 >>> 1 - b <<< 1 >>> 1) >>> 63 |||
        b >>> 63 &&& (a >>> 63 ^^^ b >>> 63) = BitVec.ofNat 64 (if a.toNat < b.toNat then 1 else 0) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [shr63_val a, shr63_val b, low63_val a, low63_val b, borrow63_val (by omega_using []) (by omega_using [])]
  have hA : a.toNat / 2 ^ 63 = 0 ∨ a.toNat / 2 ^ 63 = 1 := by omega_using []
  have hB : b.toNat / 2 ^ 63 = 0 ∨ b.toNat / 2 ^ 63 = 1 := by omega_using []
  by_cases hl : a.toNat % 2 ^ 63 < b.toNat % 2 ^ 63
  · rw [ite_eq_left hl]
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB]
    · rw [ite_eq_left (by omega_using [hl, hA])]; decide
    · rw [ite_eq_left (by omega_using [hl, hA])]; decide
    · rw [ite_eq_right (by omega_using [hA, hB])]; decide
    · rw [ite_eq_left (by omega_using [hl, hB])]; decide
  · rw [ite_eq_right hl]
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB]
    · rw [ite_eq_right (by omega_using [hl, hB])]; decide
    · rw [ite_eq_left (by omega_using [hA, hB])]; decide
    · rw [ite_eq_right (by omega_using [hl, hA])]; decide
    · rw [ite_eq_right (by omega_using [hl, hA])]; decide

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
      omega_using [hu, hl]
  · rw [ite_eq_right ho, ite_eq_right ho, ite_eq_right ho]
    refine ⟨BitVec.eq_of_toNat_eq ?_, rfl⟩
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using [hu]


/-- The condition of `modBit`'s subtraction. -/
theorem flag_val (p : Prop) [Decidable p] (a : BitVec 64) :
    BitVec.ofNat 64 (if p then 1 else 0) ^^^ BitVec.ofNat 64 1 ||| a >>> 63 =
      BitVec.ofNat 64 (if ¬p ∨ 2 ^ 63 ≤ a.toNat then 1 else 0) := by
  rw [shr63_val]
  have := a.isLt
  by_cases hp : p
  · by_cases ha : 2 ^ 63 ≤ a.toNat
    · rw [ite_eq_left hp, ite_eq_left (Or.inr ha), show a.toNat / 2 ^ 63 = 1 by omega_using [ha]]; decide
    · rw [ite_eq_left hp, ite_eq_right (fun h => h.elim (· hp) ha), show a.toNat / 2 ^ 63 = 0 by omega_using [ha]]; decide
  · rw [ite_eq_right hp, ite_eq_left (Or.inl hp)]
    have : a.toNat / 2 ^ 63 = 0 ∨ a.toNat / 2 ^ 63 = 1 := by omega_using []
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
  have hb : x / 2 ^ 63 ≤ 1 := by omega_using [hx]
  have hy : BitVec.ofNat 64 acc <<< 1 + BitVec.ofNat 64 x >>> 63 =
      BitVec.ofNat 64 (2 * acc % 2 ^ 64 + x / 2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega_using [hacc, he]),
      Nat.mod_eq_of_lt hx]
    omega_using []
  refine ⟨?_, ?_⟩
  · rw [hy, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he,
      Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega_using [hacc, he])]
    by_cases hA : 2 ^ 63 ≤ acc
    · rw [ite_eq_left (Or.inr hA)]
      have hm : (2 * acc + x / 2 ^ 63) % e = 2 * acc + x / 2 ^ 63 - e := by
        rw [Nat.mod_eq_sub_mod (by omega_using [he, hA]), Nat.mod_eq_of_lt (by omega_using [hacc, hx])]
      rw [hm]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [he, hA]
    · have hyl : (2 * acc % 2 ^ 64 + x / 2 ^ 63) % 2 ^ 64 = 2 * acc + x / 2 ^ 63 := by omega_using [hx, hA]
      rw [hyl]
      by_cases hl : 2 * acc + x / 2 ^ 63 < e
      · rw [ite_eq_right (by omega_using [he, hl]), Nat.mod_eq_of_lt hl]
        exact congrArg _ (by omega_using [hA])
      · rw [ite_eq_left (Or.inl hl)]
        have hm : (2 * acc + x / 2 ^ 63) % e = 2 * acc + x / 2 ^ 63 - e := by
          rw [Nat.mod_eq_sub_mod (by omega_using [hl]), Nat.mod_eq_of_lt (by omega_using [hacc, hx])]
        rw [hm]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega_using [hl]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hx]
    omega_using []

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-! ### `RsaKeyGen.PPC64LE.Cand.ModE`, which only this module used -/

section

/-!
# A candidate on PPC64LE: `(c − 1) mod e`

The 64 bits of a word, from the top, into `r = r3 < e = r21`: `modBits_ok`,
`r := (r 2^64 + x) mod e` (by `modBit_ok` and `shift_step`); the words of a
number from the top, `r14` walking down and `r17` counting
(`modWords_ok`): the number mod `e`. As AArch64's
(`Proof/RsaKeyGen/AArch64/ModE.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Impl.RsaKeyGen.PPC64LE.Candidate

theorem self_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

/-- A word shifted left `i` bits, `y = (x mod 2^(k + 1)) 2^i` for `k + i = 63`:
its top bit, and itself doubled modulo `2^64`. -/
theorem shift1 (x k i : Nat) (hki : k + i = 63) :
    (x % 2 ^ (k + 1)) * 2 ^ i / 2 ^ 63 = x / 2 ^ k % 2 ∧
    2 * ((x % 2 ^ (k + 1)) * 2 ^ i) % 2 ^ 64 = (x % 2 ^ k) * 2 ^ (i + 1) := by
  obtain ⟨hy, hb, hsh, -⟩ := VG.Proof.RsaKeyGen.shift_step x k i hki
  generalize (x % 2 ^ (k + 1)) * 2 ^ i = y at hy hb hsh ⊢
  refine ⟨?_, by rw [Nat.two_mul]; exact hsh⟩
  rw [← hb]
  by_cases h : 2 ^ 64 ≤ y + y
  · rw [decide_eq_true h]; show _ = 1; omega_using [hy, h]
  · rw [decide_eq_false h]; show _ = 0; omega_using [h]

/-- The registers `modBits` writes. -/
def mbRegs : List Reg := [.r0, .r3, .r4, .r6, .r7, .r8, .r9, .r15, .r16]

/-- The 64 bits of the word `x` in `r7` into `r = r3 < e` (`r21`):
`(r 2^64 + x) mod e`. -/
theorem modBits_ok {s : State} (h6 : s.gpr .r6 = BitVec.ofNat 64 64)
    (hre : (s.gpr .r3).toNat < (s.gpr .r21).toNat) :
    WP isa (Impl.Bignum.PPC64LE.Precompute.countLoop .r6 modBit) s fun t =>
      (t.gpr .r3).toNat = ((s.gpr .r3).toNat * 2 ^ 64 + (s.gpr .r7).toNat) % (s.gpr .r21).toNat ∧
      t.mem = s.mem ∧ Keep mbRegs s t := by
  obtain he0 : 0 < (s.gpr .r21).toNat := by omega_using [hre]
  obtain hX := (s.gpr .r7).isLt
  obtain hE := (s.gpr .r21).isLt
  refine WP.mono (wp_countdown (cnt := .r6) (N := 64) (by decide) (by decide)
    (fun i t => (t.gpr .r3).toNat = ((s.gpr .r3).toNat * 2 ^ i + (s.gpr .r7).toNat / 2 ^ (64 - i)) %
        (s.gpr .r21).toNat ∧
      (t.gpr .r7).toNat = ((s.gpr .r7).toNat % 2 ^ (64 - i)) * 2 ^ i ∧ t.mem = s.mem ∧
      Keep mbRegs s t) ?_ ⟨?_, ?_, rfl, Keep.refl _ _⟩ h6) fun t ⟨hr, _, hm, k⟩ => ?_
  · intro i hi t ⟨hr, hd, hm, k⟩ _
    obtain h21 : t.gpr .r21 = s.gpr .r21 := k.gpr .r21 (by decide)
    obtain hacc : (t.gpr .r3).toNat < (t.gpr .r21).toNat := by rw [h21, hr]; exact Nat.mod_lt _ he0
    refine WP.block_append_iff.mpr (WP.mono (modBit_ok (acc := (t.gpr .r3).toNat) (x := (t.gpr .r7).toNat)
      (e := (t.gpr .r21).toNat) (self_ofNat _) (self_ofNat _) (self_ofNat _) hacc (t.gpr .r21).isLt (t.gpr .r7).isLt)
      fun t₁ ⟨⟨h1, h2, h21₁, m₁⟩, k₁⟩ => ?_)
    obtain hsub : WP isa (.block [.subi .r6 .r6 1]) t₁ fun t' =>
        (t'.gpr .r6 = t₁.gpr .r6 - BitVec.ofNat 64 1 ∧ t'.mem = t₁.mem) ∧ Keep [.r6] t₁ t' := by
      refine WP.keep _ ?_ (by decide)
      prun
    refine WP.mono hsub fun t' ⟨⟨h6', m'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, hm], ?_⟩, ?_⟩
    · obtain ⟨_, _, _, hdiv⟩ := shift_step (s.gpr .r7).toNat (63 - i) i (by omega_using [hi])
      obtain ⟨hbit, _⟩ := shift1 (s.gpr .r7).toNat (63 - i) i (by omega_using [hi])
      rw [show 63 - i + 1 = 64 - i by omega_using [hi]] at hbit hdiv
      rw [k'.gpr .r3 (by decide), h1, h21, BitVec.toNat_ofNat, hd, hbit, hr,
        show 64 - (i + 1) = 63 - i by omega_using [], Nat.pow_succ,
        Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ he0) hE)]
      conv_rhs => rw [← hdiv]
      obtain hm2 : ∀ V b E : Nat, (2 * (V % E) + b) % E = (2 * V + b) % E := fun V b E => by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      rw [hm2]
      congr 1
      obtain hb2 : (s.gpr .r7).toNat / 2 ^ (63 - i) % 2 < 2 := Nat.mod_lt _ (by decide)
      generalize (s.gpr .r3).toNat = R
      generalize (s.gpr .r7).toNat / 2 ^ (64 - i) = Q
      generalize (s.gpr .r7).toNat / 2 ^ (63 - i) % 2 = b at hb2 ⊢
      rw [Nat.pow_succ, Nat.mul_add, Nat.mul_comm 2 (R * 2 ^ i), Nat.mul_assoc, Nat.mul_comm 2 Q]
      omega_using [hb2]
    · obtain ⟨_, hsh⟩ := shift1 (s.gpr .r7).toNat (63 - i) i (by omega_using [hi])
      rw [show 63 - i + 1 = 64 - i by omega_using [hi]] at hsh
      rw [k'.gpr .r7 (by decide), h2, BitVec.toNat_ofNat, hd, show 64 - (i + 1) = 63 - i by omega_using [], hsh]
      exact Nat.mod_eq_of_lt (by rw [← hsh]; exact Nat.mod_lt _ (by decide))
    · exact ((k.trans k₁).trans k').mono (by decide)
    · rw [h6', k₁.gpr .r6 (by decide)]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hX, Nat.add_zero, Nat.mod_eq_of_lt hre]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hX]
  · refine ⟨?_, hm, k⟩
    rw [hr, Nat.sub_self, Nat.pow_zero, Nat.div_one]


/-- The words `m` to `w − 1` of the number at `d`. -/
abbrev hiw (mem : Mem) (B : Addr) (d w m : Nat) : Nat := wv mem B (d + 8 * m) (w - m)

theorem hiw_step (mem : Mem) (B : Addr) (d w m : Nat) (hm : m < w) :
    hiw mem B d w m = (word mem B (d + 8 * m)).toNat + 2 ^ 64 * hiw mem B d w (m + 1) := by
  unfold hiw
  rw [show w - m = 1 + (w - (m + 1)) by omega_using [hm], wv_add,
    show d + 8 * m + 8 * 1 = d + 8 * (m + 1) by omega_using []]
  simp [wv]

/-- One word: `r14` down a word, the word into `r7`, `r6 := 64`. -/
theorem modWordHead_ok {s : State} {B : Addr} {Z d k : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B (d + 8 * (k + 1))) (hd : d + 8 * (k + 1) ≤ Z) :
    WP isa (.block [.subi .r14 .r14 8, .load .d .r7 .r14 0, .li .r6 64]) s fun t =>
      (t.gpr .r14 = off B (d + 8 * k) ∧ t.gpr .r7 = word s.mem B (d + 8 * k) ∧
        t.gpr .r6 = BitVec.ofNat 64 64 ∧ t.mem = s.mem) ∧ Keep [.r14, .r7, .r6] s t := by
  have hn := hs.nowrap
  obtain ha : off B (d + 8 * (k + 1)) - BitVec.ofNat 64 8 = off B (d + 8 * k) := by
    rw [show d + 8 * (k + 1) = d + 8 * k + 8 by omega_using []]
    show B + BitVec.ofNat 64 (d + 8 * k + 8) - BitVec.ofNat 64 8 = B + BitVec.ofNat 64 (d + 8 * k)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  refine WP.keep _ ?_ (by decide)
  prun [h14, ha, hs.ld (d := d + 8 * k) (n := 8) (by omega_using [hd])]

/-- The registers `modWords` writes. -/
def mwRegs : List Reg := [.r0, .r3, .r4, .r6, .r7, .r8, .r9, .r14, .r15, .r16, .r17]

/-- After `j` words of the loop from the top. -/
structure ModInv (s₀ : State) (B : Addr) (d w : Nat) (j : Nat) (t : State) : Prop where
  val : (t.gpr .r3).toNat = hiw s₀.mem B d w (w - j) % (s₀.gpr .r21).toNat
  r14 : t.gpr .r14 = off B (d + 8 * (w - j))
  mem : t.mem = s₀.mem
  keep : Keep mwRegs s₀ t

/-- The words of the number at `d`, from the top, into `r = r3 = 0` modulo
the `e > 1` in `r21`. -/
theorem modWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z) (h14 : s.gpr .r14 = off B (d + 8 * w))
    (h17 : s.gpr .r17 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hd : d + 8 * w ≤ Z)
    (h3 : s.gpr .r3 = 0) (he : 1 < (s.gpr .r21).toNat) :
    WP isa (.loop (.seq (.block [.subi .r14 .r14 8, .load .d .r7 .r14 0, .li .r6 64])
      (.seq (Impl.Bignum.PPC64LE.Precompute.countLoop .r6 modBit) (.block [.subi .r17 .r17 1])))
      (.nonzero .d .r17)) s fun t =>
      (t.gpr .r3).toNat = wv s.mem B d w % (s.gpr .r21).toNat ∧ t.mem = s.mem ∧ Keep mwRegs s t := by
  refine WP.mono (wp_countdown (cnt := .r17) (N := w) (by omega_using [hw']) (by omega_using [hw]) (ModInv s B d w) ?_
    ⟨by rw [h3, Nat.sub_zero]; unfold hiw; rw [Nat.sub_self]; simp [wv], by rw [h14, Nat.sub_zero], rfl,
      Keep.refl _ _⟩ h17) fun t hI => ⟨?_, hI.mem, hI.keep⟩
  · intro j hj t hI _
    obtain t21 : t.gpr .r21 = s.gpr .r21 := hI.keep.gpr .r21 (by decide)
    refine WP.seq (WP.mono (modWordHead_ok (B := B) (Z := Z) (d := d) (k := w - (j + 1)) (hs.congr hI.keep.wr)
      (by rw [hI.r14, show w - (j + 1) + 1 = w - j by omega_using [hj]]) (by omega_using [hd, hj]))
      fun t₁ ⟨⟨h14₁, h7₁, h6₁, m₁⟩, k₁⟩ => ?_)
    obtain k01 := hI.keep.trans k₁
    obtain r21 : t₁.gpr .r21 = s.gpr .r21 := k01.gpr .r21 (by decide)
    obtain r3 : t₁.gpr .r3 = t.gpr .r3 := k₁.gpr .r3 (by decide)
    refine WP.seq (WP.mono (modBits_ok h6₁ (by rw [r21, r3, hI.val]; exact Nat.mod_lt _ (by omega_using [he])))
      fun t₂ ⟨h3₂, m₂, k₂⟩ => ?_)
    obtain hsub : WP isa (.block [.subi .r17 .r17 1]) t₂ fun t' =>
        (t'.gpr .r17 = t₂.gpr .r17 - BitVec.ofNat 64 1 ∧ t'.mem = t₂.mem) ∧ Keep [.r17] t₂ t' := by
      refine WP.keep _ ?_ (by decide)
      prun
    refine WP.mono hsub fun t' ⟨⟨h17', m'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₂, m₁, hI.mem], ?_⟩, ?_⟩
    · rw [k'.gpr .r3 (by decide), h3₂, r21, r3, h7₁, hI.val, hI.mem,
        hiw_step s.mem B d w (w - (j + 1)) (by omega_using [hj]), show w - (j + 1) + 1 = w - j by omega_using [hj]]
      obtain hm2 : ∀ V x E : Nat, ((V % E) * 2 ^ 64 + x) % E = (x + 2 ^ 64 * V) % E := fun V x E => by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm, Nat.mul_comm]
      exact hm2 _ _ _
    · rw [k'.gpr .r14 (by decide), k₂.gpr .r14 (by decide), h14₁]
    · exact ((k01.trans k₂).trans k').mono (by decide)
    · rw [h17', k₂.gpr .r17 (by decide), k₁.gpr .r17 (by decide)]
  · rw [hI.val, Nat.sub_self]; unfold hiw; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end


/-!
# A candidate on PPC64LE: `gcd(c − 1, e)`

`modE_ok`: `c` (array 0) copied to `aCm1`, its low word less 1 (`c` is odd),
then its words from the top modulo the `e > 1` in `r21` (`modWords_ok`):
`r3 = (c − 1) mod e`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Impl.RsaKeyGen.PPC64LE.Candidate
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- The registers `modE` writes. -/
def meRegs : List Reg := [.r5, .r14, .r15, .r17, .r0, .r3, .r4, .r6, .r7, .r8, .r9, .r16]

theorem slot_lt' {w j k : Nat} (h : j < k) : slot w j + 8 * (w + 2) ≤ slot w k :=
  VG.Proof.MillerRabin.PPC64LE.slot_lt h

/-- A number of `w ≥ 1` words: its low word and the others. -/
theorem wv_low (m : Mem) (B : Addr) (d w : Nat) (hw : 1 ≤ w) :
    wv m B d w = (word m B d).toNat + 2 ^ 64 * wv m B (d + 8) (w - 1) := by
  rw [show w = 1 + (w - 1) by omega_using [hw], wv_add, Nat.add_sub_cancel_left]
  simp [wv]

/-- Numbers of equal words at different offsets are equal. -/
theorem wv_shift' {m m' : Mem} {B : Addr} {d d' w : Nat}
    (h : ∀ i < w, word m' B (d' + 8 * i) = word m B (d + 8 * i)) : wv m' B d' w = wv m B d w := by
  induction w with
  | zero => rfl
  | succ k ih => rw [wv, wv, ih fun i hi => h i (by omega_using [hi]), h k (by omega_using [])]

theorem modE_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z)
    (hc : wv s.mem B (slot w 0) w = c) (hodd : c % 2 = 1) (he : 1 < (s.gpr .r21).toNat) :
    WP isa modE s fun t =>
      ((t.gpr .r3).toNat = (c - 1) % (s.gpr .r21).toNat ∧ Outside B (slot w aCm1) (8 * w) s.mem t.mem) ∧
        Keep meRegs s t := by
  have hs := h.hs
  have hn := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  obtain s34 : slot w aCm1 + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt' (show aCm1 < nArr by decide)) h35
  obtain s0 : slot w 0 + 8 * (w + 2) ≤ slot w aCm1 := slot_lt' (show 0 < aCm1 by decide)
  unfold modE
  -- `r14 :=` `aCm1`, `r15 :=` array 0.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r14) (by decide) (by decide) aCm1) fun t₁ ⟨⟨a14, m₁⟩, k₁⟩ => ?_
  obtain hp : WP isa (.block [.addi .r15 .r10 0]) t₁ fun t =>
      (t.gpr .r15 = off B (slot w 0) ∧ t.mem = t₁.mem) ∧ Keep [.r15] t₁ t := by
    refine WP.keep _ ?_ (by decide)
    prun [(k₁.gpr .r10 (by decide)).trans h.h10]
  refine WP.mono hp fun t₂ ⟨⟨a15, m₂⟩, k₂⟩ => ?_
  obtain e2 := (h.keep k₁ (by decide)).keep k₂ (by decide)
  -- The copy.
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.Search.copyWithin_ok (dS := slot w 0) (dD := slot w aCm1) e2.hs a15
    (by rw [k₂.gpr .r14 (by decide), a14]) e2.h11 (by omega_using [hw4]) (by omega_using [hw128]) (by omega_using [s34, s0]) (by omega_using [s34]) (.inl (by omega_using [s0])))
    fun t₃ ⟨⟨_, hcp, out₃⟩, k₃⟩ => ?_)
  obtain e3 := e2.keep k₃ (by decide)
  -- Its low word less 1, and the loop's registers.
  obtain hm23 : t₂.mem = s.mem := by rw [m₂, m₁]
  obtain hw0 : word t₃.mem B (slot w aCm1) = word s.mem B (slot w 0) := by
    have := hcp 0 (by omega_using [hw4]); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this, hm23]
  obtain hodd0 : (word s.mem B (slot w 0)).toNat % 2 = 1 := by
    have := wv_low s.mem B (slot w 0) w (by omega_using [hw4]); rw [hc] at this; omega
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (e3.base (rd := .r14) (by decide) (by decide) aCm1) fun t₄ ⟨⟨b14, m₄⟩, k₄⟩ => ?_
  obtain hblk : WP isa (.block [.load .d .r3 .r14 0, .subi .r3 .r3 1, .store .d .r3 .r14 0, .lsl .r5 .r11 2,
      .add .r14 .r14 .r5, .lsr .d .r17 .r11 1, .li .r3 0]) t₄ fun t =>
      (t.mem = t₄.mem.writeW (off B (slot w aCm1)) (word t₄.mem B (slot w aCm1) - BitVec.ofNat 64 1) ∧
        t.gpr .r14 = off B (slot w aCm1 + 8 * w) ∧ t.gpr .r17 = BitVec.ofNat 64 w ∧ t.gpr .r3 = 0) ∧
        Keep [.r3, .r5, .r14, .r17] t₄ t := by
    refine WP.keep _ ?_ (by decide)
    obtain h11 : t₄.gpr .r11 = BitVec.ofNat 64 (2 * w) := (k₄.gpr .r11 (by decide)).trans e3.h11
    prun [b14, h11, (hs.congr (k₁.trans (k₂.trans (k₃.trans k₄))).wr).ld (d := slot w aCm1) (n := 8) (by omega_using [s34]),
      (hs.congr (k₁.trans (k₂.trans (k₃.trans k₄))).wr).st (d := slot w aCm1) (n := 8) (by omega_using [s34])]
    refine ⟨?_, ?_, rfl⟩
    · have e8 : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        omega_using []
      rw [e8]; exact off_add _ _ _
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega_using [hw128]
  refine WP.mono hblk fun t₅ ⟨⟨m₅, b14', b17, b3⟩, k₅⟩ => ?_
  obtain k15 := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  obtain e5 : (t₅.gpr .r21).toNat = (s.gpr .r21).toNat := by rw [k15.gpr .r21 (by decide)]
  refine WP.mono (modWords_ok (hs.congr k15.wr) b14' b17 (by omega_using [hw4]) (by omega_using [hw128]) (by omega_using [s34]) b3 (by rw [e5]; exact he))
    fun t ⟨tv, tm, kt⟩ => ⟨⟨?_, ?_⟩, (k15.trans kt).mono (by decide)⟩
  · rw [tv, e5, m₅, m₄]
    -- The number in `aCm1` is `c − 1`.
    obtain hv : wv (t₃.mem.writeW (off B (slot w aCm1)) (word t₃.mem B (slot w aCm1) - BitVec.ofNat 64 1)) B
        (slot w aCm1) w = c - 1 := by
      obtain hout := writeW_outside t₃.mem B (d := slot w aCm1) (word t₃.mem B (slot w aCm1) - BitVec.ofNat 64 1)
        (by omega_using [hn, s34])
      rw [wv_low _ _ _ _ (by omega_using [hw4]), word_writeW_self,
        hout.wv (d := slot w aCm1 + 8) (k := w - 1) (Or.inr (Nat.le_refl _)) (by omega_using [hn, s34])]
      obtain hrest : wv t₃.mem B (slot w aCm1 + 8) (w - 1) = wv s.mem B (slot w 0 + 8) (w - 1) := by
        rw [← hm23]
        apply wv_shift'; intro i hi
        have := hcp (i + 1) (by omega_using [hi])
        rw [show slot w aCm1 + 8 + 8 * i = slot w aCm1 + 8 * (i + 1) by omega_using [],
          show slot w 0 + 8 + 8 * i = slot w 0 + 8 * (i + 1) by omega_using []]
        exact this
      rw [hrest, BitVec.toNat_sub, hw0, BitVec.toNat_ofNat]
      obtain hcw := wv_low s.mem B (slot w 0) w (by omega_using [hw4])
      rw [hc] at hcw
      have := (word s.mem B (slot w 0)).isLt
      omega_using [hodd, hcw]
    rw [hv]
  · have o4 : Outside B (slot w aCm1) (8 * w) s.mem t₄.mem := by
      rw [m₄, ← hm23]; exact out₃
    rw [tm, m₅]
    exact o4.trans ((writeW_outside t₄.mem B (d := slot w aCm1) _ (by omega_using [hn, s34])).mono (by omega_using []) (by omega_using [hw4]))


theorem gcdStep_lt {u v : Nat} (hu : u < 2 ^ 64) (hv : v < 2 ^ 64) :
    (VG.Proof.RsaKeyGen.gcdStep u v).1 < 2 ^ 64 ∧ (VG.Proof.RsaKeyGen.gcdStep u v).2 < 2 ^ 64 := by
  unfold VG.Proof.RsaKeyGen.gcdStep
  split
  · split <;> exact ⟨by omega, by omega⟩
  · exact ⟨by omega, hv⟩

theorem gcdIter_lt : ∀ n {u v : Nat}, u < 2 ^ 64 → v < 2 ^ 64 → v % 2 = 1 →
    (VG.Proof.RsaKeyGen.gcdIter n u v).1 < 2 ^ 64 ∧ (VG.Proof.RsaKeyGen.gcdIter n u v).2 < 2 ^ 64 ∧
      (VG.Proof.RsaKeyGen.gcdIter n u v).2 % 2 = 1
  | 0, _, _, hu, hv, ho => ⟨hu, hv, ho⟩
  | n + 1, u, v, hu, hv, ho => by
    rw [VG.Proof.RsaKeyGen.gcdIter]
    exact gcdIter_lt n (gcdStep_lt hu hv).1 (gcdStep_lt hu hv).2 (VG.Proof.RsaKeyGen.gcdStep_odd ho)

/-- The registers the gcd's steps write. -/
def gsRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r9, .r15, .r16, .r21]

/-- 128 steps of the binary gcd from `u = r3` and the odd `v = r21`. -/
theorem gcdLoop_ok {s : State} {u v : Nat} (h3 : s.gpr .r3 = BitVec.ofNat 64 u)
    (h21 : s.gpr .r21 = BitVec.ofNat 64 v) (h9 : s.gpr .r9 = BitVec.ofNat 64 128) (hu : u < 2 ^ 64)
    (hv : v < 2 ^ 64) (ho : v % 2 = 1) :
    WP isa (Impl.Bignum.PPC64LE.Precompute.countLoop .r9 VG.Impl.RsaKeyGen.PPC64LE.Candidate.gcdStep) s fun t =>
      t.gpr .r21 = BitVec.ofNat 64 (Nat.gcd u v) ∧ t.mem = s.mem ∧ Keep gsRegs s t := by
  refine WP.mono (wp_countdown (cnt := .r9) (N := 128) (by decide) (by decide)
    (fun i t => t.gpr .r3 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdIter i u v).1 ∧
      t.gpr .r21 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdIter i u v).2 ∧ t.mem = s.mem ∧ Keep gsRegs s t)
    ?_ ⟨h3, h21, rfl, Keep.refl _ _⟩ h9) fun t ⟨_, t21, tm, tk⟩ => ⟨?_, tm, tk⟩
  · intro i _ t ⟨t3, t21, tm, tk⟩ _
    obtain ⟨b1, b2, bo⟩ := gcdIter_lt i hu hv ho
    refine WP.block_append_iff.mpr (WP.mono (gcdStep_ok t3 t21 b1 b2 bo) fun t₁ ⟨⟨a3, a21, m₁⟩, k₁⟩ => ?_)
    obtain hsub : WP isa (.block [.subi .r9 .r9 1]) t₁ fun t' =>
        (t'.gpr .r9 = t₁.gpr .r9 - BitVec.ofNat 64 1 ∧ t'.mem = t₁.mem) ∧ Keep [.r9] t₁ t' := by
      refine WP.keep _ ?_ (by decide)
      prun
    refine WP.mono hsub fun t' ⟨⟨h9', m'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, tm], ?_⟩, ?_⟩
    · rw [k'.gpr .r3 (by decide), a3, VG.Proof.RsaKeyGen.gcdIter_succ']
    · rw [k'.gpr .r21 (by decide), a21, VG.Proof.RsaKeyGen.gcdIter_succ']
    · exact ((tk.trans k₁).trans k').mono (by decide)
    · rw [h9', k₁.gpr .r9 (by decide)]
  · rw [t21, VG.Proof.RsaKeyGen.gcdIter_eq 128 u v ho (by
      have : u * v < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_lt_of_lt hu hv
      rw [← Nat.pow_add] at this; exact this)]


/-- `gcdE`: `r22 := gcd(c − 1, e) − 1` for the odd `e > 1` in `r21`. -/
theorem gcdE_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z)
    (hc : wv s.mem B (slot w 0) w = c) (hodd : c % 2 = 1) (he : 1 < (s.gpr .r21).toNat)
    (heo : (s.gpr .r21).toNat % 2 = 1) :
    WP isa gcdE s fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (Nat.gcd (c - 1) (s.gpr .r21).toNat) - BitVec.ofNat 64 1 ∧
        Outside B (slot w aCm1) (8 * w) s.mem t.mem) ∧ Keep (meRegs ++ gsRegs ++ ([.r22] : List Reg)) s t := by
  unfold gcdE
  refine WP.seq (WP.mono (modE_ok h h35 hc hodd he) fun t₁ ⟨⟨v₁, o₁⟩, k₁⟩ => ?_)
  obtain e₁ : t₁.gpr .r21 = s.gpr .r21 := k₁.gpr .r21 (by decide)
  obtain h9 : WP isa (.block [.li .r9 128]) t₁ fun t =>
      (t.gpr .r9 = BitVec.ofNat 64 128 ∧ t.mem = t₁.mem) ∧ Keep [.r9] t₁ t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.seq (WP.mono h9 fun t₂ ⟨⟨a9, m₂⟩, k₂⟩ => ?_)
  obtain hE := (s.gpr .r21).isLt
  refine WP.seq (WP.mono (gcdLoop_ok (u := (c - 1) % (s.gpr .r21).toNat) (v := (s.gpr .r21).toNat)
    (by rw [k₂.gpr .r3 (by decide), ← v₁]; exact self_ofNat _)
    (by rw [k₂.gpr .r21 (by decide), e₁]; exact self_ofNat _) a9
    (Nat.lt_trans (Nat.mod_lt _ (by omega_using [he])) hE) hE heo) fun t₃ ⟨g₃, m₃, k₃⟩ => ?_)
  obtain hsub : WP isa (.block [.subi .r22 .r21 1]) t₃ fun t =>
      (t.gpr .r22 = t₃.gpr .r21 - BitVec.ofNat 64 1 ∧ t.mem = t₃.mem) ∧ Keep [.r22] t₃ t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.mono hsub fun t ⟨⟨a22, m⟩, k⟩ => ⟨⟨?_, ?_⟩, ((k₁.trans k₂).trans (k₃.trans k)).mono (by decide)⟩
  · rw [a22, g₃, show Nat.gcd ((c - 1) % (s.gpr .r21).toNat) (s.gpr .r21).toNat = Nat.gcd (c - 1) (s.gpr .r21).toNat
      from by rw [← Nat.gcd_rec, Nat.gcd_comm]]
  · rw [m, m₃, m₂]; exact o₁


theorem os2ip_bytes_lt (m : Mem) (E : Addr) : ∀ i, Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E i) < 256 ^ i
  | 0 => by simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip]
  | i + 1 => by
    rw [VG.Proof.Bignum.PPC64LE.Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc, Nat.pow_succ]
    have := os2ip_bytes_lt m E i
    have := (m (off E i)).isLt
    omega_arith

/-- `loadE`: `e`'s `L` octets (`1 ≤ L ≤ 8`) at `E` (`r21`, `r30`) into `r21`. -/
theorem loadE_ok {s : State} {E : Addr} {L : Nat} (h21 : s.gpr .r21 = off E 0)
    (h30 : s.gpr .r30 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L ≤ 8)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off E i) 1) :
    WP isa loadE s fun t =>
      (t.gpr .r21 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E L)) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r14, .r17, .r21] s t := by
  unfold loadE
  refine WP.seq ?_
  obtain hpre : WP isa (.block [.li .r3 0, .addi .r14 .r21 0, .addi .r17 .r30 0]) s fun s₁ =>
      (s₁.gpr .r3 = 0 ∧ s₁.gpr .r14 = off E 0 ∧ s₁.gpr .r17 = BitVec.ofNat 64 L ∧ s₁.mem = s.mem) ∧
        Keep [.r3, .r14, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h21, h30]
    exact ⟨rfl, BitVec.add_zero _⟩
  refine WP.mono hpre fun s₁ ⟨⟨i3, i14, i17, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r3 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E i)) ∧
      t.gpr .r14 = off E i ∧ t.mem = s.mem ∧ Keep [.r0, .r3, .r14, .r17] s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .r17) (N := L) (by omega_using [hL']) (by omega_using [hL]) Inv
    (fun i hi t ⟨t3, t14, tm, tk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, i14, im, k₁.mono⟩ i17) fun t ⟨t3, _, tm, tk⟩ => ?_)
  · have hb : InRegions (t.rd ++ t.wr) (off E i) 1 := by rw [tk.rd, tk.wr]; exact hrd i hi
    refine WP.mono (WP.keep [.r0, .r3, .r14, .r17] (Q := fun t' =>
      t'.gpr .r3 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E (i + 1))) ∧
        t'.gpr .r14 = off E (i + 1) ∧ t'.mem = t.mem ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) ?_ (by decide))
      fun t' ⟨⟨a, b, c, d⟩, k⟩ => ⟨⟨a, b, c.trans tm, tk.trans' k⟩, d⟩
    prun [t14, t3, exec_lbz' (show Reg.r14 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hb, read_byte64]
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.Bignum.PPC64LE.Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc, tm, BitVec.toNat_add,
      BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    obtain hbt := (s.mem (VG.Proof.Mont.off E i)).isLt
    obtain hlt := os2ip_bytes_lt s.mem E i
    obtain h256 : 256 ^ i ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_using [hL', hi])
    have : (256 : Nat) ^ 7 = 2 ^ 56 := by decide
    rw [Nat.mod_eq_of_lt (show Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E i) < 2 ^ 64 by omega_using [hlt, h256])]
    omega_using []
  · have hfin : WP isa (.block [.addi .r21 .r3 0]) t fun t' =>
        (t'.gpr .r21 = t.gpr .r3 ∧ t'.mem = t.mem) ∧ Keep [.r21] t t' := by
      refine WP.keep _ ?_ (by decide)
      prun
      exact BitVec.add_zero _
    exact WP.mono hfin fun t' ⟨⟨a, b⟩, k⟩ => ⟨⟨a.trans t3, b.trans tm⟩, (tk.trans k).mono (by decide)⟩


/-- The registers `gcdCheck` writes. -/
def gcRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r14, .r15, .r16, .r17, .r21, .r22]

/-- `gcdCheck`: `r22 = 0` iff `gcd(c − 1, e) = 1`, for `e` the `L` octets at
`E` (`r21`, `r30`). -/
theorem gcdCheck_ok {s : State} {B E : Addr} {Z w c L : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z)
    (hc : wv s.mem B (slot w 0) w = c) (hodd : c % 2 = 1) (h21 : s.gpr .r21 = off E 0)
    (h30 : s.gpr .r30 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L ≤ 8)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off E i) 1) :
    WP isa gcdCheck s fun t =>
      ((t.gpr .r22 = 0 ↔ Nat.gcd (c - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E L)) = 1) ∧
        Outside B (slot w aCm1) (8 * w) s.mem t.mem) ∧ Keep gcRegs s t := by
  obtain hEl : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E L) < 2 ^ 64 := by
    have := os2ip_bytes_lt s.mem E L
    have : 256 ^ L ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hL'
    have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega_arith
  generalize hEv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E L) = e at hEl ⊢
  unfold gcdCheck
  refine WP.seq (WP.mono (loadE_ok h21 h30 hL hL' hrd) fun t₁ ⟨⟨e₁, m₁⟩, k₁⟩ => ?_)
  rw [hEv] at e₁
  obtain hb : WP isa (.block [.li .r0 1, .logic .and .r5 .r21 .r0]) t₁ fun t =>
      (t.gpr .r5 = BitVec.ofNat 64 (e % 2) ∧ t.gpr .r21 = t₁.gpr .r21 ∧ t.mem = t₁.mem) ∧ Keep [.r0, .r5] t₁ t := by
    refine WP.keep _ ?_ (by decide)
    prun [e₁, and1_val]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hEl]
    split <;> (congr 1; omega_arith)
  refine WP.seq (WP.mono hb fun t₂ ⟨⟨a5, a21, m₂⟩, k₂⟩ => ?_)
  obtain k12 := k₁.trans k₂
  obtain hm2 : t₂.mem = s.mem := by rw [m₂, m₁]
  refine WP.ite _ (eval_zero_ofNat _ _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)) a5)
    (fun hz => ?_) (fun hz => ?_)
  · -- `e` even.
    obtain he2 : e % 2 = 0 := by simpa using hz
    obtain hblk : WP isa (.block [.li .r22 1]) t₂ fun t =>
        (t.gpr .r22 = BitVec.ofNat 64 1 ∧ t.mem = t₂.mem) ∧ Keep [.r22] t₂ t := by
      refine WP.keep _ ?_ (by decide)
      prun
    refine WP.mono hblk fun t ⟨⟨a22, m⟩, k⟩ => ⟨⟨?_, by rw [m, hm2]; exact Outside.refl _ _ _ _⟩, (k12.trans k).mono (by decide)⟩
    rw [a22]
    refine ⟨fun h => absurd h (by decide), fun hg => ?_⟩
    have : 2 ∣ Nat.gcd (c - 1) e := Nat.dvd_gcd (by omega_using [hodd]) (by omega_using [he2])
    rw [hg] at this; exact absurd this (by decide)
  · have he1 : e % 2 = 1 := by simp at hz; omega_using [hz]
    obtain hsub : WP isa (.block [.subi .r5 .r21 1]) t₂ fun t =>
        (t.gpr .r5 = BitVec.ofNat 64 (e - 1) ∧ t.mem = t₂.mem) ∧ Keep [.r5] t₂ t := by
      refine WP.keep _ ?_ (by decide)
      prun [a21, e₁]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [he1]
    refine WP.seq (WP.mono hsub fun t₃ ⟨⟨a5', m₃⟩, k₃⟩ => ?_)
    obtain k13 := k12.trans k₃
    refine WP.ite _ (eval_zero_ofNat _ _ (by omega_using [hEl]) a5') (fun hz' => ?_) (fun hz' => ?_)
    · have he' : e = 1 := by simp at hz'; omega_using [he1, hz']
      obtain hblk : WP isa (.block [.li .r22 0]) t₃ fun t =>
          (t.gpr .r22 = 0 ∧ t.mem = t₃.mem) ∧ Keep [.r22] t₃ t := by
        refine WP.keep _ ?_ (by decide)
        prun
        rfl
      refine WP.mono hblk fun t ⟨⟨a22, m⟩, k⟩ =>
        ⟨⟨?_, by rw [m, m₃, hm2]; exact Outside.refl _ _ _ _⟩, (k13.trans k).mono (by decide)⟩
      rw [a22, he', Nat.gcd_one_right]; exact ⟨fun _ => rfl, fun _ => rfl⟩
    · have he' : 1 < e := by simp at hz'; omega_using [hz']
      obtain env3 : Env t₃ B Z w := h.keep k13 (by decide)
      obtain hc3 : wv t₃.mem B (slot w 0) w = c := by rw [m₃, hm2]; exact hc
      obtain r21 : t₃.gpr .r21 = BitVec.ofNat 64 e := (k₃.gpr .r21 (by decide)).trans (a21.trans e₁)
      obtain hev : (t₃.gpr .r21).toNat = e := by rw [r21, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hEl]
      refine WP.mono (gcdE_ok env3 h35 hc3 hodd (by rw [hev]; exact he') (by rw [hev]; exact he1))
        fun t ⟨⟨a22, o⟩, k⟩ => ⟨⟨?_, by rw [m₃, hm2] at o; exact o⟩, (k13.trans k).mono (by decide)⟩
      rw [a22, hev]
      obtain hg1 : 1 ≤ Nat.gcd (c - 1) e := Nat.gcd_pos_of_pos_right _ (by omega_using [he1])
      obtain hg2 : Nat.gcd (c - 1) e ≤ e := Nat.gcd_le_right _ (by omega_using [he1])
      constructor
      · intro hz0
        obtain hn : (BitVec.ofNat 64 (Nat.gcd (c - 1) e) - BitVec.ofNat 64 1).toNat = Nat.gcd (c - 1) e - 1 := by
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hEl, hg1, hg2]
        rw [hz0] at hn
        have : (0 : BitVec 64).toNat = 0 := rfl
        omega
      · intro hg; rw [hg]; rfl

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-! ### `RsaKeyGen.PPC64LE.Cand.Close`, which this module and modules that import it used -/

section

/-!
# A candidate on PPC64LE: too close to `p`

`sub_ok`: `[o] := [a] − [b]` by `subMod`, its borrow's mask in `r20`.
`closeCheck_ok`: `r22` is whether `c` (array 0) is too close to `p`, the
`p_len` octets at `P` (`r18`, `r19`): `|c − p| ≤ 2^(64 w − 100)`, by `c − p`,
`p − c`, the one that does not borrow, and the borrow of the bound minus it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (seqs sub loadP closeCalc closeCheck aP aD1 aD2 aAbs aBnd aTmp nArr)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Bignum (slot wv)

/-- The registers `sub` writes. -/
def subRegs : List Reg := [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20]

/-- `sub o a b`: `[o] := [a] − [b]`, with the borrow `c`, for `[a]` whose
digit `2 w` is zero; the mask of `c` in `r20`. -/
theorem sub_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z) {o a b : Nat}
    (ho : o < nArr) (ha : a < nArr) (hb : b < nArr) (hoa : o ≠ a) (hob : o ≠ b)
    (hz : w32 s.mem B (slot w a + 8 * w) = 0) :
    WP isa (sub o a b) s fun t =>
      (∃ c ≤ 1, val32 t.mem B (slot w o) (2 * w) + val32 s.mem B (slot w b) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) + 2 ^ (64 * w) * c ∧ t.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 c) ∧
        Env t B Z w ∧ Outside B (slot w o) (8 * w) s.mem t.mem ∧ Keep subRegs s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  obtain hO := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) ho) h35
  obtain hA := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) ha) h35
  obtain hB := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) hb) h35
  obtain soa := VG.Proof.Bignum.slot_sep (w := w) hoa
  obtain sob := VG.Proof.Bignum.slot_sep (w := w) hob
  unfold sub
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .r8) (by decide) (by decide) a) fun t₁ ⟨⟨a8, m₁⟩, k₁⟩ => ?_
  obtain e₁ := h.keep k₁ (by decide)
  refine WP.mono (e₁.base (rd := .r9) (by decide) (by decide) o) fun t₂ ⟨⟨a9, m₂⟩, k₂⟩ => ?_
  obtain e₂ := e₁.keep k₂ (by decide)
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) e₂.h10 e₂.h29 b) fun t₃ ⟨⟨a10, m₃⟩, k₃⟩ => ?_
  obtain hm : t₃.mem = s.mem := by rw [m₃, m₂, m₁]
  obtain k13 := (k₁.trans k₂).trans k₃
  obtain hs₃ := h.hs.congr k13.wr
  refine WP.seq (WP.mono (subMod_ok hs₃ (dA := slot w a) (dT := slot w o) (dM := slot w b) (n := 2 * w)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), a8]) (by rw [k₃.gpr _ (by decide), a9]) a10
    (by rw [k13.gpr _ (by decide)]; exact h.h11) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t₄ ⟨⟨c, hc, hv, h20⟩, out₄, k₄⟩ => ?_)
  rw [hm] at hv h20 out₄
  rw [show slot w a + 4 * (2 * w) = slot w a + 8 * w by omega_arith, hz] at h20
  obtain k14 := k13.trans k₄
  refine WP.mono (WP.keep [.r10] (Q := fun u => u.gpr .r10 = off B (slot w 0) ∧ u.mem = t₄.mem) (by
    prun [(k14.gpr .r31 (by decide)).trans h.h31, VG.Impl.Bignum.hdrBytes]
    show B + BitVec.ofNat 64 256 = B + BitVec.ofNat 64 (slot w 0)
    rw [slot0]) (by decide)) fun t ⟨⟨t10, tm⟩, kt⟩ => ?_
  obtain K := k14.trans kt
  refine ⟨⟨c, hc, ?_, ?_⟩, ⟨h.hs.congr K.wr, t10, ?_, ?_, ?_, hw4, hw128, h.hZ⟩, ?_, K.mono (by simp [subRegs])⟩
  · rw [tm, show 64 * w = 32 * (2 * w) by omega_arith]; exact hv
  · rw [kt.gpr _ (by decide), h20]
    rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl <;> rfl
  · rw [K.gpr _ (by decide)]; exact h.h29
  · rw [K.gpr _ (by decide)]; exact h.h11
  · rw [K.gpr _ (by decide)]; exact h.h31
  · rw [tm, show 8 * w = 4 * (2 * w) by omega_arith]; exact out₄

/-- An array apart from the `w` words of another that changed keeps its value. -/
theorem out_val {B : Addr} {w o j : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * w) m m') (hj : j ≠ o)
    (hn : slot w nArr ≤ 2 ^ 64) (hj' : j < nArr) :
    val32 m' B (slot w j) (2 * w) = val32 m B (slot w j) (2 * w) := by
  have := VG.Proof.Bignum.slot_sep (w := w) hj
  have := VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) hj'
  have := slot_le (w := w) (show j + 1 ≤ nArr by omega_arith)
  exact h.val32 (by omega_arith) (by omega_arith)

/-- Digit `2 w` of an array, which no change of the `w` words of an array
reaches. -/
theorem out_top {B : Addr} {w o j : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * w) m m')
    (hn : slot w nArr ≤ 2 ^ 64) (ho : o < nArr) (hj : j < nArr) :
    w32 m' B (slot w j + 8 * w) = w32 m B (slot w j + 8 * w) := by
  have := VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) hj
  have := slot_le (w := w) (show j + 1 ≤ nArr by omega_arith)
  by_cases e : j = o
  · subst e; exact h.w32 (by omega_arith) (by omega_arith)
  · have := VG.Proof.Bignum.slot_sep (w := w) e
    exact h.w32 (by omega_arith) (by omega_arith)

/-- `loadP`: `p`'s `8 w` octets at `P` (`r18`) into `aP`. -/
theorem loadP_ok {s : State} {B P : Addr} {Z w : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z) (h18 : s.gpr .r18 = P)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w)) (hP : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : ∀ i < 8 * w, ∀ x, ofs B x < Z → off P i ≠ x) :
    WP isa loadP s fun t =>
      (val32 t.mem B (slot w aP) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P (8 * w)) ∧
        Env t B Z w ∧ Outside B (slot w aP) (8 * w) s.mem t.mem) ∧
        Keep [.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  obtain hA := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) (show aP < nArr by decide)) h35
  unfold loadP
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) h.h10 h.h29 aP) fun t₁ ⟨⟨a10, m₁⟩, k₁⟩ => ?_
  obtain hpre : WP isa (.block [.addi .r12 .r18 0, .addi .r6 .r24 0]) t₁ fun u =>
      (u.gpr .r12 = off P 0 ∧ u.gpr .r6 = BitVec.ofNat 64 (8 * w) ∧ u.mem = t₁.mem) ∧ Keep [.r6, .r12] t₁ u := by
    refine WP.keep _ ?_ (by decide)
    prun [(k₁.gpr _ (by decide)).trans h18, (k₁.gpr _ (by decide)).trans h24]
    exact BitVec.add_zero _
  refine WP.mono hpre fun u ⟨⟨u12, u6, um⟩, ku⟩ => ?_
  obtain k1u := k₁.trans ku
  refine WP.seq (WP.mono (loadN_ok (h.hs.congr k1u.wr) (dA := slot w aP) ((ku.gpr _ (by decide)).trans a10) u12 u6
    (by rw [k1u.gpr _ (by decide)]; exact h.h11) (by omega_arith) (Nat.le_refl _) (by omega_arith)
    (by simp only [slot, VG.Impl.Bignum.hdrBytes]; omega_arith) (by omega_arith) (fun i hi => by rw [k1u.rd, k1u.wr]; exact hP i hi) hsep)
    fun v ⟨vv, vout, kv⟩ => ?_)
  rw [um, m₁] at vv vout
  obtain k1v := k1u.trans kv
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = v.mem) (by
    prun [(k1v.gpr .r31 (by decide)).trans h.h31, VG.Impl.Bignum.hdrBytes]
    show B + BitVec.ofNat 64 256 = B + BitVec.ofNat 64 (slot w 0)
    rw [slot0]) (by decide)) fun t ⟨⟨t10, tm⟩, kt⟩ => ?_
  obtain K := k1v.trans kt
  refine ⟨⟨by rw [tm]; exact vv, ⟨h.hs.congr K.wr, t10, ?_, ?_, ?_, hw4, hw128, h.hZ⟩, by rw [tm]; exact vout⟩,
    K.mono (by simp)⟩
  · rw [K.gpr _ (by decide)]; exact h.h29
  · rw [K.gpr _ (by decide)]; exact h.h11
  · rw [K.gpr _ (by decide)]; exact h.h31

/-- A number of words all zero but word `k`. -/
theorem wv_single {m : Mem} {p : Addr} {d k : Nat} {v : BitVec 64}
    (hk : VG.Proof.Bignum.word m p (d + 8 * k) = v) :
    ∀ n, (∀ i < n, i ≠ k → VG.Proof.Bignum.word m p (d + 8 * i) = 0) →
      wv m p d n = if k < n then v.toNat * 2 ^ (64 * k) else 0
  | 0, _ => by simp [wv]
  | n + 1, hz => by
    rw [wv, wv_single hk n fun i hi hik => hz i (by omega_arith) hik]
    by_cases e : n = k
    · subst e; rw [hk]; simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self, Nat.zero_add]
      exact Nat.mul_comm _ _
    · rw [hz n (by omega_arith) e]
      by_cases hl : k < n
      · simp only [hl, ↓reduceIte, show k < n + 1 by omega_arith]; simp
      · simp only [hl, ↓reduceIte, show ¬ k < n + 1 by omega_arith]; simp

theorem lis_eq : BitVec.signExtend 64 ((4096 : BitVec 16) ++ (0 : BitVec 16)) = (268435456#64 : BitVec 64) := by
  decide

/-- The bound `2^(64 w − 100)` into `aBnd`: word `w − 2` := `2^28`. -/
theorem bound_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z) :
    WP isa (.block (base .r5 aBnd ++ ([.lsl .r6 .r11 2, .add .r5 .r5 .r6, .subi .r5 .r5 16, .lis .r0 0x1000,
      .store .d .r0 .r5 0] : List Instr))) s fun t =>
      (t.mem = s.mem.writeW (off B (slot w aBnd + 8 * (w - 2))) (BitVec.ofNat 64 (2 ^ 28))) ∧
        Keep [.r0, .r5, .r6] s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  obtain hA := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) (show aBnd < nArr by decide)) h35
  have hnw := h.hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r5) (by decide) (by decide) aBnd) fun t₁ ⟨⟨a5, m₁⟩, k₁⟩ => ?_
  obtain hs₁ := h.hs.congr k₁.wr
  obtain e5 : off B (slot w aBnd) + (BitVec.ofNat 64 (2 * w) <<< 2) - BitVec.ofNat 64 16 =
      off B (slot w aBnd + 8 * (w - 2)) := by
    obtain e8 : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_arith
    rw [e8, off_add, Offset.add_ofNat_sub _ (show 16 ≤ slot w aBnd + 8 * w by omega_arith),
      show slot w aBnd + 8 * w - 16 = slot w aBnd + 8 * (w - 2) by omega_arith]
  obtain hst := hs₁.st (d := slot w aBnd + 8 * (w - 2)) (n := 8) (by omega_arith)
  refine WP.mono (WP.keep [.r0, .r5, .r6] (Q := fun t =>
      t.mem = t₁.mem.writeW (off B (slot w aBnd + 8 * (w - 2))) (BitVec.ofNat 64 (2 ^ 28))) ?_ (by decide))
    fun t ⟨tm, kt⟩ => ⟨by rw [tm, m₁], (k₁.trans kt).mono⟩
  prun [a5, (k₁.gpr _ (by decide)).trans h.h11, exec_lis, lis_eq, e5, hst]
  done

/-- A change within one of the arrays `aP` to `aTmp`. -/
theorem into_close {B : Addr} {w j n : Nat} {m m' : Mem} (h : Outside B (slot w j) n m m') (hj : aP ≤ j)
    (hj' : j ≤ aTmp) (hn : n ≤ 8 * (w + 2)) : Outside B (slot w aP) (6 * (8 * (w + 2))) m m' := by
  simp only [aP, aTmp] at hj hj'
  refine h.mono ?_ ?_
  · rw [slot_lin, slot_lin]; have := Nat.mul_le_mul_right (8 * w) hj; simp only [aP] at this ⊢; omega_arith
  · rw [slot_lin, slot_lin]; have := Nat.mul_le_mul_right (8 * w) hj'; simp only [aP] at this ⊢; omega_arith

/-- The registers the check writes. -/
def ccRegs : List Reg := [.r0, .r3, .r5, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r20, .r22]

/-- The borrow of `x − y` for `x, y < R`, from `D + y = x + R b` with `D < R`. -/
theorem borrow_iff {x y D R b : Nat} (hb : b ≤ 1) (h : D + y = x + R * b) (hD : D < R) (hy : y < R) :
    (b = 1 ↔ x < y) ∧ (b = 0 → D = x - y) ∧ (b = 1 → D = R + x - y) := by
  rcases (show b = 0 ∨ b = 1 by omega_arith) with rfl | rfl <;> omega_arith

theorem flag_final (b : Nat) (hb : b ≤ 1) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 b) &&& BitVec.ofNat 64 1 ^^^ BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (if b = 1 then 0 else 1) := by
  rcases (show b = 0 ∨ b = 1 by omega_arith) with rfl | rfl <;> decide

/-- The check's arithmetic: `|c − p|` from the differences, and the bound's
borrow. -/
theorem close_math {c p D1 D2 A T Bd R b1 b2 b3 : Nat} (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1)
    (hb3 : b3 ≤ 1) (h1 : D1 + p = c + R * b1) (hD1 : D1 < R) (h2 : D2 + c = p + R * b2) (hD2 : D2 < R)
    (hA : A = if b1 = 1 then D2 else D1) (h3 : T + A = Bd + R * b3) (hT : T < R) :
    (if b3 = 1 then 0 else 1) = if Spec.RsaKeyGen.absDiff c p ≤ Bd then 1 else 0 := by
  obtain eA : A = Spec.RsaKeyGen.absDiff c p := by
    unfold Spec.RsaKeyGen.absDiff
    rcases (show b1 = 0 ∨ b1 = 1 by omega_arith) with rfl | rfl <;>
      rcases (show b2 = 0 ∨ b2 = 1 by omega_arith) with rfl | rfl <;>
      simp only [hA, Nat.reduceEqDiff, ↓reduceIte] <;> split <;> omega_arith
  rw [← eA]
  obtain hAR : A < R := by rw [hA]; split <;> omega_arith
  rcases (show b3 = 0 ∨ b3 = 1 by omega_arith) with rfl | rfl
  · simp only [show ¬ (0 = 1) by decide, ↓reduceIte]; rw [ite_eq_left (by omega_arith)]
  · simp only [↓reduceIte]; rw [ite_eq_right (by omega_arith)]

theorem closeCalc_ok {s : State} {B P : Addr} {Z w c : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z)
    (hc : val32 s.mem B (slot w 0) (2 * w) = c) (hz0 : w32 s.mem B (slot w 0 + 8 * w) = 0)
    (hzP : w32 s.mem B (slot w aP + 8 * w) = 0)
    (hzB : ∀ i < w + 1, VG.Proof.Bignum.word s.mem B (slot w aBnd + 8 * i) = 0)
    (h18 : s.gpr .r18 = P) (h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w))
    (hP : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : ∀ i < 8 * w, ∀ x, ofs B x < Z → off P i ≠ x) :
    WP isa (seqs closeCalc) s fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if Spec.RsaKeyGen.absDiff c (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P (8 * w))) ≤
          2 ^ (64 * w - 100) then 1 else 0) ∧
        Env t B Z w ∧ Outside B (slot w aP) (6 * (8 * (w + 2))) s.mem t.mem) ∧ Keep ccRegs s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  have hnw := h.hs.nowrap
  obtain hn : slot w nArr ≤ 2 ^ 64 := by omega_arith
  obtain es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain h35' : 256 + 35 * (8 * w) + 35 * 16 ≤ Z := by rw [← slot_lin]; exact h35
  obtain zD2 : slot w aD2 + 4 * (2 * w) ≤ Z := by rw [slot_lin]; simp only [aD2]; omega_arith
  obtain zD1 : slot w aD1 + 4 * (2 * w) ≤ Z := by rw [slot_lin]; simp only [aD1]; omega_arith
  obtain zAb : slot w aAbs + 4 * (2 * w) ≤ Z := by rw [slot_lin]; simp only [aAbs]; omega_arith
  obtain zAD2 : slot w aAbs + 4 * (2 * w) ≤ slot w aD2 ∨ slot w aD2 + 4 * (2 * w) ≤ slot w aAbs := by
    rw [slot_lin, slot_lin]; simp only [aAbs, aD2]; omega_arith
  obtain zAD1 : slot w aAbs + 4 * (2 * w) ≤ slot w aD1 ∨ slot w aD1 + 4 * (2 * w) ≤ slot w aAbs := by
    rw [slot_lin, slot_lin]; simp only [aAbs, aD1]; omega_arith
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P (8 * w)) = p
  obtain hpR : p < 2 ^ (64 * w) := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem P (8 * w))
    rw [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq, hp, show 8 * (8 * w) = 64 * w by omega_arith] at this
    exact this
  obtain hcR : c < 2 ^ (64 * w) := by
    have := val32_lt s.mem B (slot w 0) (2 * w); rw [hc, show 32 * (2 * w) = 64 * w by omega_arith] at this; exact this
  -- `p`.
  unfold closeCalc
  rw [wp_seqs (by simp)]
  refine WP.mono (loadP_ok h h35 h18 h24 hP hsep) fun t₁ ⟨⟨vP, e₁, o₁⟩, k₁⟩ => ?_
  rw [hp] at vP
  obtain c₁ : val32 t₁.mem B (slot w 0) (2 * w) = c := by rw [out_val o₁ (by decide) hn (by decide), hc]
  obtain z₁ : w32 t₁.mem B (slot w 0 + 8 * w) = 0 := by rw [out_top o₁ hn (by decide) (by decide), hz0]
  obtain zP₁ : w32 t₁.mem B (slot w aP + 8 * w) = 0 := by rw [out_top o₁ hn (by decide) (by decide), hzP]
  -- `c − p`.
  rw [wp_seqs (by simp)]
  refine WP.mono (sub_ok e₁ h35 (o := aD1) (a := 0) (b := aP) (by decide) (by decide) (by decide) (by decide)
    (by decide) z₁) fun t₂ ⟨⟨b1, hb1, v₂, r₂⟩, e₂, o₂, k₂⟩ => ?_
  rw [c₁, vP] at v₂
  have hs₂ := e₂.hs
  obtain k12 := k₁.trans k₂
  -- `r22 :=` the mask of `c < p`.
  rw [wp_seqs (by simp)]
  refine WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = t₂.gpr .r20 ∧ u.mem = t₂.mem) (by
    prun []; exact BitVec.add_zero _) (by decide)) fun t₃ ⟨⟨r22₃, m₃⟩, k₃⟩ => ?_
  obtain e₃ := e₂.keep k₃ (by decide)
  obtain vP₃ : val32 t₃.mem B (slot w aP) (2 * w) = p := by rw [m₃, out_val o₂ (by decide) hn (by decide), vP]
  obtain c₃ : val32 t₃.mem B (slot w 0) (2 * w) = c := by rw [m₃, out_val o₂ (by decide) hn (by decide), c₁]
  obtain zP₃ : w32 t₃.mem B (slot w aP + 8 * w) = 0 := by rw [m₃, out_top o₂ hn (by decide) (by decide), zP₁]
  -- `p − c`.
  rw [wp_seqs (by simp)]
  refine WP.mono (sub_ok e₃ h35 (o := aD2) (a := aP) (b := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) zP₃) fun t₄ ⟨⟨b2, hb2, v₄, r₄⟩, e₄, o₄, k₄⟩ => ?_
  rw [c₃, vP₃] at v₄
  obtain d1₄ : val32 t₄.mem B (slot w aD1) (2 * w) = val32 t₂.mem B (slot w aD1) (2 * w) := by
    rw [out_val o₄ (by decide) hn (by decide), m₃]
  obtain r22₄ : t₄.gpr .r22 = BitVec.ofNat 64 0 - BitVec.ofNat 64 b1 := by
    rw [k₄.gpr _ (by decide), r22₃, r₂]
  -- `|c − p|`, the difference that does not borrow.
  rw [wp_seqs (by simp), WP.seq_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e₄.base (rd := .r8) (by decide) (by decide) aD2) fun u₁ ⟨⟨a8, mu₁⟩, ku₁⟩ => ?_
  obtain eu₁ := e₄.keep ku₁ (by decide)
  refine WP.mono (eu₁.base (rd := .r9) (by decide) (by decide) aD1) fun u₂ ⟨⟨a9, mu₂⟩, ku₂⟩ => ?_
  obtain eu₂ := eu₁.keep ku₂ (by decide)
  refine WP.mono (eu₂.base (rd := .r5) (by decide) (by decide) aAbs) fun u₃ ⟨⟨a5, mu₃⟩, ku₃⟩ => ?_
  obtain eu₃ := eu₂.keep ku₃ (by decide)
  obtain ku13 := (ku₁.trans ku₂).trans ku₃
  refine WP.mono (WP.keep [.r20] (Q := fun u => u.gpr .r20 = u₃.gpr .r22 ∧ u.mem = u₃.mem) (by
    prun []; exact BitVec.add_zero _) (by decide)) fun u₄ ⟨⟨a20, mu₄⟩, ku₄⟩ => ?_
  obtain eu₄ := eu₃.keep ku₄ (by decide)
  obtain hmu : u₄.mem = t₄.mem := by rw [mu₄, mu₃, mu₂, mu₁]
  obtain ku14 := ku13.trans ku₄
  refine WP.mono (selectAcc_ok eu₄.hs (dA := slot w aD2) (dT := slot w aD1) (dO := slot w aAbs) (n := 2 * w)
    (b := decide (b1 = 1)) (by rw [ku₄.gpr _ (by decide), ku₃.gpr _ (by decide), ku₂.gpr _ (by decide), a8])
    (by rw [ku₄.gpr _ (by decide), ku₃.gpr _ (by decide), a9]) (by rw [ku₄.gpr _ (by decide), a5]) eu₄.h11
    (by rw [a20, ku13.gpr _ (by decide), r22₄]; rcases (show b1 = 0 ∨ b1 = 1 by omega_arith) with rfl | rfl <;> rfl)
    (by omega_arith) (by omega_arith) zD2 zD1 zAb zAD2 zAD1) fun t₅ ⟨v₅, o₅, k₅⟩ => ?_
  rw [hmu, d1₄] at v₅
  rw [hmu] at o₅
  obtain e₅ := eu₄.keep k₅ (by decide)
  -- The bound.
  obtain wB : ∀ i < w + 1, VG.Proof.Bignum.word t₅.mem B (slot w aBnd + 8 * i) = 0 := by
    intro i hi
    obtain l1 : slot w aBnd = slot w aP + 4 * (8 * (w + 2)) := by rw [slot_lin, slot_lin]; simp only [aBnd, aP]; omega_arith
    obtain hb : slot w aBnd + 8 * i + 8 ≤ Z := by rw [slot_lin]; simp only [aBnd]; omega_arith
    show word t₅.mem B (slot w aBnd + 8 * i) = 0
    rw [o₅.word (by rw [slot_lin, slot_lin]; simp only [aAbs, aBnd]; omega_arith) (by omega_arith),
      o₄.word (by rw [slot_lin, slot_lin]; simp only [aD2, aBnd]; omega_arith) (by omega_arith), m₃,
      o₂.word (by rw [slot_lin, slot_lin]; simp only [aD1, aBnd]; omega_arith) (by omega_arith),
      o₁.word (by rw [slot_lin, slot_lin]; simp only [aP, aBnd]; omega_arith) (by omega_arith)]
    exact hzB i hi
  rw [wp_seqs (by simp)]
  refine WP.mono (bound_ok e₅ h35) fun t₆ ⟨m₆, k₆⟩ => ?_
  obtain e₆ := e₅.keep k₆ (by decide)
  obtain hB2 : slot w aBnd + 8 * (w - 2) + 8 ≤ Z := by rw [slot_lin]; simp only [aBnd]; omega_arith
  obtain hBw : slot w aBnd + 8 * (w + 1) ≤ Z := by rw [slot_lin]; simp only [aBnd]; omega_arith
  obtain vB : val32 t₆.mem B (slot w aBnd) (2 * w) = 2 ^ (64 * w - 100) := by
    rw [Pre.val32_eq_wv, wv_single (k := w - 2) (v := BitVec.ofNat 64 (2 ^ 28)) (by
        show t₆.mem.readW _ 64 = _; rw [m₆, Mem.readW_writeW_self64]) w (fun i hi hik => by
        show t₆.mem.readW _ 64 = 0
        rw [m₆, Mem.readW_writeW_sep (Offset.sep B (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact wB i (by omega_arith)), ite_eq_left (by omega_arith)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), ← Nat.pow_add]
    congr 1; omega_arith
  obtain zB₆ : w32 t₆.mem B (slot w aBnd + 8 * w) = 0 := by
    obtain e := word_eq_w32 t₆.mem B (slot w aBnd + 8 * w)
    obtain z : word t₆.mem B (slot w aBnd + 8 * w) = 0 := by
      show t₆.mem.readW _ 64 = 0
      rw [m₆, Mem.readW_writeW_sep (Offset.sep B (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact wB w (by omega_arith)
    obtain z' : (word t₆.mem B (slot w aBnd + 8 * w)).toNat = 0 := by rw [z]; rfl
    omega_arith
  obtain vA₆ : val32 t₆.mem B (slot w aAbs) (2 * w) = val32 t₅.mem B (slot w aAbs) (2 * w) := by
    rw [m₆]
    exact (writeW_outside t₅.mem B (d := slot w aBnd + 8 * (w - 2)) _ (by omega_arith)).val32
      (by rw [slot_lin, slot_lin]; simp only [aAbs, aBnd]; omega_arith) (by omega_arith)
  -- The bound's borrow.
  rw [wp_seqs (by simp)]
  refine WP.mono (sub_ok e₆ h35 (o := aTmp) (a := aBnd) (b := aAbs) (by decide) (by decide) (by decide)
    (by decide) (by decide) zB₆) fun t₇ ⟨⟨b3, hb3, v₇, r₇⟩, e₇, o₇, k₇⟩ => ?_
  rw [vA₆, vB, v₅] at v₇
  refine WP.mono (WP.keep [.r0, .r22] (Q := fun t => t.gpr .r22 =
      (t₇.gpr .r20 &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1 ∧ t.mem = t₇.mem) (by prun []) (by decide))
    fun t ⟨⟨r22, tm⟩, kt⟩ => ?_
  obtain R := Nat.two_pow_pos (64 * w)
  obtain lt32 : ∀ (m : Mem) (j : Nat), val32 m B (slot w j) (2 * w) < 2 ^ (64 * w) := fun m j => by
    have := val32_lt m B (slot w j) (2 * w); rwa [show 32 * (2 * w) = 64 * w by omega_arith] at this
  refine ⟨⟨?_, e₇.keep kt (by decide), ?_⟩, ?_⟩
  · rw [r22, r₇, flag_final b3 hb3]
    congr 1
    exact close_math hb1 hb2 hb3 v₂ (lt32 _ _) v₄ (lt32 _ _) (by simp only [decide_eq_true_eq]) v₇ (lt32 _ _)
  · rw [tm]
    obtain l8 : 8 * w ≤ 8 * (w + 2) := Nat.mul_le_mul_left 8 (Nat.le_add_right w 2)
    obtain i1 := into_close o₁ (Nat.le_refl _) (by decide) l8
    obtain i2 := into_close o₂ (by decide) (by decide) l8
    obtain i4 := into_close o₄ (by decide) (by decide) l8
    obtain i5 := into_close o₅ (by decide) (by decide) (by rw [show 4 * (2 * w) = 8 * w by omega_arith]; exact l8)
    obtain i6 : Outside B (slot w aP) (6 * (8 * (w + 2))) t₅.mem t₆.mem := by
      rw [m₆]
      refine (writeW_outside t₅.mem B (d := slot w aBnd + 8 * (w - 2)) (BitVec.ofNat 64 (2 ^ 28)) (by omega_arith)).mono
        ?_ ?_
      · rw [slot_lin, slot_lin]; simp only [aP, aBnd]; omega_arith
      · rw [slot_lin, slot_lin]; simp only [aP, aBnd]; omega_arith
    obtain i7 := into_close o₇ (by decide) (Nat.le_refl _) l8
    exact (((((i1.trans i2).trans (by rw [← m₃]; exact i4)).trans i5).trans i6).trans i7)
  · exact (((((((((((k₁.trans k₂).trans k₃).trans k₄).trans ku₁).trans ku₂).trans ku₃).trans ku₄).trans k₅).trans
      k₆).trans k₇).trans kt).mono (by simp [ccRegs, subRegs])

end VG.Proof.RsaKeyGen.PPC64LE.Cand

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (seqs closeCalc closeCheck aP aBnd nArr)
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Bignum (slot)

/-- `closeCheck`: `r22` is whether `c` is too close to `p`, the `p_len`
octets at `P` (none for `p_len = 0`). -/
theorem closeCheck_ok {s : State} {B P : Addr} {Z w c pL : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z)
    (hc : val32 s.mem B (slot w 0) (2 * w) = c) (hz0 : w32 s.mem B (slot w 0 + 8 * w) = 0)
    (hzP : w32 s.mem B (slot w aP + 8 * w) = 0)
    (hzB : ∀ i < w + 1, VG.Proof.Bignum.word s.mem B (slot w aBnd + 8 * i) = 0)
    (h18 : s.gpr .r18 = P) (h19 : s.gpr .r19 = BitVec.ofNat 64 pL) (hpL : pL = 0 ∨ pL = 8 * w)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w))
    (hP : pL = 8 * w → ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : pL = 8 * w → ∀ i < 8 * w, ∀ x, ofs B x < Z → off P i ≠ x) :
    WP isa closeCheck s fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if Spec.RsaKeyGen.tooClose (64 * w)
          (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem P pL)) c then 1 else 0) ∧
        Env t B Z w ∧ Outside B (slot w aP) (6 * (8 * (w + 2))) s.mem t.mem) ∧ Keep ccRegs s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  unfold closeCheck
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega_arith) h19) (fun hz => ?_) (fun hz => ?_)
  · have e0 : pL = 0 := by simpa using hz
    subst e0
    refine WP.mono (WP.keep [.r22] (Q := fun t => t.gpr .r22 = 0 ∧ t.mem = s.mem) (by prun []; rfl) (by decide))
      fun t ⟨⟨t22, tm⟩, kt⟩ => ⟨⟨?_, h.keep kt (by decide), by rw [tm]; exact Outside.refl _ _ _ _⟩,
        kt.mono (by simp [ccRegs])⟩
    rw [t22]
    simp [Spec.RsaKeyGen.otherPrime, Spec.Rsa.bytesAt, Spec.RsaKeyGen.tooClose]
  · have e0 : pL = 8 * w := by simp at hz; omega_arith
    subst e0
    refine WP.mono (closeCalc_ok h h35 hc hz0 hzP hzB h18 h24 (hP rfl) (hsep rfl)) fun t ⟨⟨t22, et, ot⟩, kt⟩ =>
      ⟨⟨?_, et, ot⟩, kt⟩
    rw [t22]
    obtain hne : Spec.Rsa.bytesAt s.mem P (8 * w) ≠ [] := by
      intro e; have := congrArg List.length e
      rw [VG.Proof.Bignum.bytesAt_length] at this; simp at this; omega_arith
    simp only [Spec.RsaKeyGen.otherPrime, hne, ↓reduceIte, Spec.RsaKeyGen.tooClose, decide_eq_true_eq]

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-!
# A candidate on PPC64LE: whether a draw is at least 2

`atLeast2_ok`: `r21 := 1` if the draw `x` in array 4 is at least 2, else 0,
from `x₀ >> 1` or'ed with its other words.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (atLeast2 toThree uniform)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- Whether a word is zero, as a flag: `((a & 1) | (a >> 1)) − 1`'s top bit,
inverted. -/
theorem flag_ne0 (a : BitVec 64) :
    (((a &&& BitVec.ofNat 64 1) ||| a >>> 1) - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (if a = 0 then 0 else 1) := by
  have ha := a.isLt
  obtain e1 : (a &&& BitVec.ofNat 64 1).toNat = a.toNat % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_comm, Nat.one_and_eq_mod_two]
  obtain e2 : (a >>> 1).toNat = a.toNat / 2 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  obtain hb : ((a &&& BitVec.ofNat 64 1) ||| a >>> 1).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_or, e1, e2]; exact Nat.or_lt_two_pow (by omega_using []) (by omega_using [])
  obtain hz : ((a &&& BitVec.ofNat 64 1) ||| a >>> 1) = 0 ↔ a = 0 := by
    constructor
    · intro h
      obtain h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_or, e1, e2, show (0 : BitVec 64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at h'
      exact BitVec.eq_of_toNat_eq (by simp; omega_using [h'])
    · intro h; subst h; decide
  generalize ((a &&& BitVec.ofNat 64 1) ||| a >>> 1) = b at hb hz
  obtain hb' : b = BitVec.ofNat 64 b.toNat := by simp
  rw [hb', borrow63_val hb (show 1 < 2 ^ 63 by decide)]
  by_cases h : a = 0
  · have : b.toNat = 0 := by rw [hz.mpr h]; rfl
    rw [ite_eq_left (by omega_using [this]), ite_eq_left h]; decide
  · have : b.toNat ≠ 0 := fun e => h (hz.mp (BitVec.eq_of_toNat_eq (by rw [e]; rfl)))
    rw [ite_eq_right (by omega_using [this]), ite_eq_right h]; decide

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    obtain h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, show (0 : BitVec 64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at h'
    exact ⟨BitVec.eq_of_toNat_eq h'.1, BitVec.eq_of_toNat_eq h'.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem shr1_eq_zero (a : BitVec 64) : a >>> 1 = 0 ↔ a &&& (BitVec.allOnes 64 - 1) = 0 := by
  rw [VG.Proof.RsaKeyGen.and_m2_eq_zero]
  constructor
  · intro h
    obtain h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h'
    simp at h'; omega_using [h']
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp; omega_using [h]

/-- `atLeast2`: `r21 := 1` if array 4 holds at least 2, else 0. -/
theorem atLeast2_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa atLeast2 s fun t =>
      (t.gpr .r21 = BitVec.ofNat 64 (if 2 ≤ wv s.mem B (slot w 4) w then 1 else 0) ∧ t.mem = s.mem ∧
        Env t B Z w) ∧ Keep [.r0, .r3, .r5, .r6, .r21] s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  rw [slot_lin] at hZ
  obtain s4 : slot w 4 + 8 * w ≤ Z := by rw [slot_lin]; omega_using [hZ]
  unfold atLeast2
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r5) (by decide) (by decide) 4) fun t₁ ⟨⟨a5, m₁⟩, k₁⟩ => ?_
  obtain hs₁ := hs.congr k₁.wr
  refine WP.mono (WP.keep [.r5, .r6, .r21] (Q := fun t => t.gpr .r21 = word s.mem B (slot w 4) >>> 1 ∧
      t.gpr .r5 = off B (slot w 4 + 8 * 1) ∧ t.gpr .r6 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) ?_ (by decide))
    fun t₂ ⟨⟨b21, b5, b6, m₂⟩, k₂⟩ => ?_
  · have h11 : t₁.gpr .r11 = BitVec.ofNat 64 (2 * w) := (k₁.gpr _ (by decide)).trans h.h11
    obtain e6 : BitVec.ofNat 64 (2 * w) >>> 1 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (w - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      omega_using [hw4, hw128]
    prun [a5, h11, e6, hs₁.ld (d := slot w 4) (n := 8) (by omega_using [hw4, s4]), m₁]
  obtain k12 := k₁.trans k₂
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r21 = 0 ↔ (word s.mem B (slot w 4) >>> 1 = 0 ∧
        ∀ j, 1 ≤ j → j ≤ i → word s.mem B (slot w 4 + 8 * j) = 0)) ∧
      t.gpr .r5 = off B (slot w 4 + 8 * (i + 1)) ∧ t.mem = s.mem ∧ Keep [.r0, .r3, .r5, .r6, .r21] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .r3 .r5 0, .logic .or .r21 .r21 .r3,
      .addi .r5 .r5 8] ++ ([.subi .r6 .r6 1] : List Instr))) (cnt := .r6) (N := w - 1) (by omega_using [hw128]) (by omega_using [hw4]) Inv
    (fun i hi t ⟨tz, t5, tm, tk⟩ _ => ?_)
    ⟨by rw [b21]; exact ⟨fun e => ⟨e, fun j h1 h2 => absurd h2 (by omega_using [h1])⟩, fun e => e.1⟩, b5, m₂, k12.mono⟩ b6)
    fun t ⟨tz, _, tm, tk⟩ => ?_)
  · have hst : WP isa (.block [.load .d .r3 .r5 0, .logic .or .r21 .r21 .r3, .addi .r5 .r5 8, .subi .r6 .r6 1]) t
        fun t' => (t'.gpr .r21 = t.gpr .r21 ||| word s.mem B (slot w 4 + 8 * (i + 1)) ∧
          t'.gpr .r5 = off B (slot w 4 + 8 * (i + 1 + 1)) ∧ t'.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem) ∧ Keep [.r3, .r5, .r6, .r21] t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [t5, (hs.congr tk.wr).ld (d := slot w 4 + 8 * (i + 1)) (n := 8) (by omega_using [s4, hi]), tm]
      rw [show slot w 4 + 8 * (i + 1) + 8 = slot w 4 + 8 * (i + 1 + 1) by omega_using []]
    refine WP.mono hst fun t' ⟨⟨u21, u5, u6, um⟩, uk⟩ => ⟨⟨?_, u5, um.trans tm, tk.trans' uk.mono⟩, u6⟩
    rw [u21, or_eq_zero, tz]
    constructor
    · rintro ⟨⟨e0, ej⟩, ei⟩
      refine ⟨e0, fun j h1 h2 => ?_⟩
      rcases Nat.lt_or_ge j (i + 1) with hj | hj
      · exact ej j h1 (by omega_using [hj])
      · rw [show j = i + 1 by omega_using [h2, hj]]; exact ei
    · rintro ⟨e0, ej⟩
      exact ⟨⟨e0, fun j h1 h2 => ej j h1 (by omega_using [h2])⟩, ej (i + 1) (by omega_using []) (Nat.le_refl _)⟩
  · refine WP.mono (WP.keep [.r0, .r3, .r21] (Q := fun u => u.gpr .r21 =
        (((t.gpr .r21 &&& BitVec.ofNat 64 1) ||| t.gpr .r21 >>> 1) - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 ∧
        u.mem = t.mem) (by prun []) (by decide)) fun u ⟨⟨u21, um⟩, ku⟩ => ?_
    obtain K := tk.trans ku
    refine ⟨⟨?_, um.trans tm, h.keep K (by decide)⟩, K.mono (by simp)⟩
    rw [u21, flag_ne0]
    obtain hle := VG.Proof.RsaKeyGen.wv_le_one (m := s.mem) (p := B) (d := slot w 4) (w := w) (by omega_using [hw4])
    rw [← shr1_eq_zero] at hle
    obtain e : (t.gpr .r21 = 0) ↔ wv s.mem B (slot w 4) w ≤ 1 := by
      rw [tz, hle]
      exact ⟨fun ⟨a, b⟩ => ⟨a, fun i h1 h2 => b i h1 (by omega_using [h2])⟩, fun ⟨a, b⟩ => ⟨a, fun j h1 h2 => b j h1 (by omega_using [hw4, h2])⟩⟩
    by_cases hz : t.gpr .r21 = 0
    · rw [ite_eq_left hz, ite_eq_right (by have := e.mp hz; omega_using [this])]
    · rw [ite_eq_right hz, ite_eq_left (by have := mt e.mpr hz; omega_using [this])]

/-- `toThree`: array 4's `w` words into array 3, and its word `w` := 0. -/
theorem toThree_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa toThree s fun t =>
      ((∀ i < w, word t.mem B (slot w 3 + 8 * i) = word s.mem B (slot w 4 + 8 * i)) ∧
        word t.mem B (slot w 3 + 8 * w) = 0 ∧ Outside B (slot w 3) (8 * w + 8) s.mem t.mem ∧ Env t B Z w) ∧
        Keep [.r0, .r5, .r6, .r14, .r15, .r17] s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  rw [slot_lin] at hZ
  unfold toThree
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r14) (by decide) (by decide) 3) fun t₁ ⟨⟨a14, m₁⟩, k₁⟩ => ?_
  obtain e₁ := h.keep k₁ (by decide)
  refine WP.mono (e₁.base (rd := .r15) (by decide) (by decide) 4) fun t₂ ⟨⟨a15, m₂⟩, k₂⟩ => ?_
  obtain e₂ := e₁.keep k₂ (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.Search.copyWithin_ok e₂.hs (dS := slot w 4) (dD := slot w 3)
    a15 (by rw [k₂.gpr _ (by decide), a14]) e₂.h11 (by omega_using [hw4]) (by omega_using [hw128]) (by rw [slot_lin]; omega_using [hZ])
    (by rw [slot_lin]; omega_using [hZ]) (by rw [slot_lin, slot_lin]; omega_using [])) fun t₃ ⟨⟨_, hc, o₃⟩, k₃⟩ => ?_)
  obtain e₃ := e₂.keep k₃ (by decide)
  obtain hm2 : t₂.mem = s.mem := by rw [m₂, m₁]
  rw [WP.block_append_iff]
  refine WP.mono (e₃.base (rd := .r5) (by decide) (by decide) 3) fun t₄ ⟨⟨a5, m₄⟩, k₄⟩ => ?_
  obtain e₄ := e₃.keep k₄ (by decide)
  obtain e8 : off B (slot w 3) + BitVec.ofNat 64 (2 * w) <<< 2 = off B (slot w 3 + 8 * w) := by
    rw [show BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_using [], off_add]
  refine WP.mono (WP.keep [.r0, .r5, .r6] (Q := fun t => t.mem = t₄.mem.writeW (off B (slot w 3 + 8 * w)) (0 : BitVec 64))
    (by prun [a5, e₄.h11, e8, e₄.hs.st (d := slot w 3 + 8 * w) (n := 8) (by rw [slot_lin]; omega_using [hZ])]; rfl)
    (by decide)) fun t ⟨tm, kt⟩ => ?_
  obtain K := (((k₁.trans k₂).trans k₃).trans k₄).trans kt
  obtain wo := writeW_outside t₄.mem B (d := slot w 3 + 8 * w) (0 : BitVec 64) (by rw [slot_lin]; omega_using [hw128])
  refine ⟨⟨fun i hi => ?_, ?_, ?_, e₄.keep kt (by decide)⟩, K.mono (by simp)⟩
  · rw [tm, wo.word (by omega_using [hi]) (by rw [slot_lin]; omega_using [hw128, hi]), m₄, hc i hi, hm2]
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm, ← hm2, m₄]
    rw [m₄] at wo
    exact (o₃.mono (o' := slot w 3) (n' := 8 * w + 8) (Nat.le_refl _) (by omega_using [])).trans
      (wo.mono (o' := slot w 3) (n' := 8 * w + 8) (by omega_using []) (by omega_using []))

theorem or1_nat (a : Nat) : a ||| 1 = a + (1 - a % 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  rcases i with _ | i
  · simp [Nat.testBit_zero]; omega_using []
  · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp
    congr 1; omega_using []

theorem mask_and1 (b : Nat) (hb : b ≤ 1) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 b) &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 b := by
  rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;> decide

/-- The registers `uniform` writes. -/
def uniRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r14, .r15, .r16, .r17, .r20, .r21]

/-- `uniform`: `r21 := 1` if the draw `x` in array 4 is a uniform witness for
`c` in array 0 (`2 ≤ x < c − 1`, as `x + (1 − x mod 2) < c`), else 0. -/
theorem uniform_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (h35 : slot w VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr ≤ Z)
    (hc : wv s.mem B (slot w 0) w = c) (hcR : c < 2 ^ (64 * w)) :
    WP isa uniform s fun t =>
      (t.gpr .r21 = BitVec.ofNat 64 (if 2 ≤ wv s.mem B (slot w 4) w ∧
          wv s.mem B (slot w 4) w + (1 - wv s.mem B (slot w 4) w % 2) < c then 1 else 0) ∧
        Env t B Z w ∧ VG.Proof.Mont.Outs B [(slot w 3, 8 * w + 8), (slot w 6, 8 * w)] s.mem t.mem) ∧ Keep uniRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h35
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr] at hZ
  rw [slot_lin] at hZ
  generalize hx : wv s.mem B (slot w 4) w = x
  unfold uniform
  refine WP.seq (WP.mono (atLeast2_ok h) fun t₁ ⟨⟨a21, m₁, e₁⟩, k₁⟩ => ?_)
  rw [hx] at a21
  refine WP.seq (WP.mono (toThree_ok e₁) fun t₂ ⟨⟨c3, z3, o₂, e₂⟩, k₂⟩ => ?_)
  rw [m₁] at c3 o₂
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e₂.base (rd := .r5) (by decide) (by decide) 3) fun t₃ ⟨⟨a5, m₃⟩, k₃⟩ => ?_
  obtain e₃ := e₂.keep k₃ (by decide)
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.mem = t₃.mem.writeW (off B (slot w 3))
      (word t₃.mem B (slot w 3) ||| BitVec.ofNat 64 1) ∧ t.gpr .r5 = t₃.gpr .r5) (by
    prun [a5, e₃.hs.ld (d := slot w 3) (n := 8) (by rw [slot_lin]; omega_using [hZ]),
      e₃.hs.st (d := slot w 3) (n := 8) (by rw [slot_lin]; omega_using [hZ])]) (by decide)) fun t₄ ⟨⟨m₄, _⟩, k₄⟩ => ?_
  obtain e₄ := e₃.keep k₄ (by decide)
  refine WP.mono (e₄.base (rd := .r8) (by decide) (by decide) 3) fun t₅ ⟨⟨a8, m₅⟩, k₅⟩ => ?_
  obtain e₅ := e₄.keep k₅ (by decide)
  refine WP.mono (e₅.base (rd := .r9) (by decide) (by decide) 6) fun t₆ ⟨⟨a9, m₆⟩, k₆⟩ => ?_
  obtain e₆ := e₅.keep k₆ (by decide)
  obtain hm6 : t₆.mem = t₄.mem := by rw [m₆, m₅]
  obtain k16 := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆)
  -- The numbers subtracted.
  obtain w0 : word t₃.mem B (slot w 3) = word s.mem B (slot w 4) := by
    rw [m₃]; have := c3 0 (by omega_using [hw4]); simpa using this
  obtain hA : wv t₆.mem B (slot w 3) w = x + (1 - x % 2) := by
    rw [hm6, m₄, wv_low _ _ _ _ (by omega_using [hw4]), word_writeW_self, w0]
    obtain hrest : wv (t₃.mem.writeW (off B (slot w 3)) (word s.mem B (slot w 4) ||| BitVec.ofNat 64 1)) B
        (slot w 3 + 8) (w - 1) = wv s.mem B (slot w 4 + 8) (w - 1) := by
      apply wv_shift'; intro i hi
      rw [(writeW_outside t₃.mem B (d := slot w 3) _ (by rw [slot_lin]; omega_using [hw128])).word (by omega_using [])
        (by rw [slot_lin]; omega_using [hw128, hi]), m₃,
        show slot w 3 + 8 + 8 * i = slot w 3 + 8 * (i + 1) by omega_using [],
        show slot w 4 + 8 + 8 * i = slot w 4 + 8 * (i + 1) by omega_using []]
      exact c3 (i + 1) (by omega_using [hi])
    rw [hrest]
    obtain hx' := wv_low s.mem B (slot w 4) w (by omega_using [hw4])
    rw [hx] at hx'
    rw [BitVec.toNat_or, show (BitVec.ofNat 64 1).toNat = 1 from rfl, or1_nat]
    have : (word s.mem B (slot w 4)).toNat % 2 = x % 2 := by omega_using [hx']
    omega_using [hx']
  obtain zA : VG.Proof.Mont.w32 t₆.mem B (slot w 3 + 4 * (2 * w)) = 0 := by
    obtain e := VG.Proof.Mont.word_eq_w32 t₆.mem B (slot w 3 + 8 * w)
    obtain z : VG.Proof.Mont.word t₆.mem B (slot w 3 + 8 * w) = 0 := by
      show t₆.mem.readW _ 64 = 0
      rw [hm6, m₄, Mem.readW_writeW_sep (Offset.sep B (by omega_using [hw4]) (by rw [slot_lin]; omega_using [hw128])
        (by rw [slot_lin]; omega_using [hw128])) (by decide), m₃]
      exact z3
    obtain z' : (VG.Proof.Mont.word t₆.mem B (slot w 3 + 8 * w)).toNat = 0 := by rw [z]; rfl
    rw [show slot w 3 + 4 * (2 * w) = slot w 3 + 8 * w by omega_using []]
    omega_using [e, z']
  obtain hM : wv t₆.mem B (slot w 0) w = c := by
    rw [← hc, hm6, m₄, ← Pre.val32_eq_wv, ← Pre.val32_eq_wv]
    rw [(VG.Proof.Mont.writeW_outside t₃.mem B (d := slot w 3) _ (by rw [slot_lin]; omega_using [hw128])).val32 (by rw [slot_lin, slot_lin]; omega_using [])
      (by rw [slot_lin]; omega_using [hw128]), m₃, VG.Proof.Mont.Outside.val32 o₂ (by rw [slot_lin, slot_lin]; omega_using [])
      (by rw [slot_lin]; omega_using [hw128])]
  refine WP.seq (WP.mono (subMod_ok e₆.hs (dA := slot w 3) (dT := slot w 6) (dM := slot w 0) (n := 2 * w)
    (by rw [k₆.gpr _ (by decide), a8]) a9 e₆.h10 e₆.h11 (by omega_using [hw4]) (by omega_using [hw128]) (by rw [slot_lin]; omega_using [hZ])
    (by rw [slot_lin]; omega_using [hZ]) (by rw [slot_lin]; omega_using [hZ]) (by rw [slot_lin, slot_lin]; omega_using [])
    (by rw [slot_lin, slot_lin]; omega_using [])) fun t₇ ⟨⟨b, hb, v₇, r₇⟩, o₇, k₇⟩ => ?_)
  rw [zA] at r₇
  simp only [Pre.val32_eq_wv] at v₇
  rw [hA, hM, show 32 * (2 * w) = 64 * w by omega_using []] at v₇
  refine WP.mono (WP.keep [.r0, .r3, .r21] (Q := fun t => t.gpr .r21 = t₇.gpr .r21 &&& (t₇.gpr .r20 &&&
      BitVec.ofNat 64 1) ∧ t.mem = t₇.mem) (by prun []) (by decide)) fun t ⟨⟨t21, tm⟩, kt⟩ => ?_
  obtain K := (k16.trans k₇).trans kt
  obtain hD := VG.Proof.Mont.val32_lt t₇.mem B (slot w 6) (2 * w)
  rw [Pre.val32_eq_wv, show 32 * (2 * w) = 64 * w by omega_using []] at hD
  obtain bi := (borrow_iff hb v₇ hD hcR).1
  refine ⟨⟨?_, ⟨hs.congr K.wr, ?_, ?_, ?_, ?_, hw4, hw128, h.hZ⟩, ?_⟩, K.mono (by simp [uniRegs])⟩
  · have r21₇ : t₇.gpr .r21 = t₁.gpr .r21 :=
      ((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).gpr .r21 (by decide))
    rw [t21, r₇, show (if 0 < b then 1 else 0) = b by rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;> rfl,
      mask_and1 b hb, r21₇, a21]
    by_cases h2 : 2 ≤ x
    · rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl
      · rw [ite_eq_left h2, ite_eq_right (fun hh => absurd (bi.mpr hh.2) (by decide))]; decide
      · rw [ite_eq_left h2, ite_eq_left ⟨h2, bi.mp rfl⟩]; decide
    · rw [ite_eq_right h2, ite_eq_right (fun hh => h2 hh.1)]
      rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;> decide
  · rw [K.gpr _ (by decide)]; exact h.h10
  · rw [K.gpr _ (by decide)]; exact h.h29
  · rw [K.gpr _ (by decide)]; exact h.h11
  · rw [K.gpr _ (by decide)]; exact h.h31
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hy
    rw [tm, o₇ y (by omega_using [hy]), hm6, m₄, VG.Proof.Mont.writeW_outside t₃.mem B (d := slot w 3) _
      (by rw [slot_lin]; omega_using [hw128]) y (by omega_using [hy]), m₃, o₂ y hy.1]

end VG.Proof.RsaKeyGen.PPC64LE.Cand
