import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.RsaKeyGen.Gcd
import VerifiedGarbage.Proof.RsaKeyGen.CandMath

/-!
# A candidate on AArch64: a step of the binary gcd, and a bit of `(c − 1) mod e`

`bgcdStep` is `gcdStep` on `u = x3` and `v = x13` (`bgcdStep_ok`, by
`gstep_bv`), 128 of them `gcdIter` (`gcdLoop_ok`); `modBit` is
`r := (2 r + bit) mod e` on `r = x3` and `e = x13` for the bit shifted out
of the top of `x2` (`modBit_ok`, by `modbit_bv`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem one16 : (1#16).setWidth 64 = (1 : BitVec 64) := rfl

theorem xor_cancel_l (a b : BitVec 64) : a ^^^ (b ^^^ a) = b := by
  rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem not_sub_allOnes (d : BitVec 64) : (d ^^^ BitVec.allOnes 64) - BitVec.allOnes 64 = -d := by
  rw [BitVec.xor_allOnes, BitVec.neg_eq_not_add, BitVec.sub_eq_add_neg]
  congr 1

theorem xor_z (x : BitVec 64) : x ^^^ 0 = x := by simp
theorem z_xor (x : BitVec 64) : 0 ^^^ x = x := by simp
theorem and_z (x : BitVec 64) : x &&& 0 = 0 := by simp
theorem sub_z (x : BitVec 64) : x - 0 = x := by simp

theorem shr1_toNat (x : BitVec 64) : (x >>> 1).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem and1_toNat (u : BitVec 64) : (u &&& 1).toNat = u.toNat % 2 := by
  rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]

/-- `0 − (u & 1)`: the mask of `u` odd. -/
theorem odd_mask' (u : BitVec 64) : 0 - (u &&& 1) = mask (decide (u.toNat % 2 = 1)) := by
  apply BitVec.eq_of_toNat_eq
  have := and1_toNat u
  by_cases h : u.toNat % 2 = 1
  · simp only [h, decide_true, mask_true]
    rw [BitVec.toNat_sub, this, h]; rfl
  · simp only [h, decide_false, mask_false]
    rw [BitVec.toNat_sub, this, show u.toNat % 2 = 0 by omega]; rfl

/-- `u + ~v + 1 = u − v`. -/
theorem add_not_one (u v : BitVec 64) : u + ~~~v + BitVec.ofNat 64 true.toNat = u - v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_ofNat, Bool.toNat_true]
  have := u.isLt; have := v.isLt; omega

/-- The borrow of `u − v` as a mask: all ones iff `u < v`. -/
theorem lt_sel (u v : BitVec 64) :
    (if decide (2 ^ 64 ≤ u.toNat + (~~~v).toNat + true.toNat) = true then (0 : BitVec 64) else mask true) =
      mask (decide (u.toNat < v.toNat)) := by
  rw [BitVec.toNat_not, show true.toNat = 1 from rfl]
  have := v.isLt
  by_cases h : u.toNat < v.toNat
  · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
  · rw [decide_eq_true (by omega), decide_eq_false h]; rfl

/-- One step of the binary gcd with masks, on words. -/
theorem gstep_bv (u v : BitVec 64) :
    let lt := mask (decide (u.toNat < v.toNat))
    let od := mask (decide (u.toNat % 2 = 1))
    ((u ^^^ ((((u - v ^^^ lt) - lt) ^^^ u) &&& od)) >>> 1).toNat = (gcdStep u.toNat v.toNat).1 ∧
      (v ^^^ ((((u ^^^ v) &&& lt) ^^^ v ^^^ v) &&& od)).toNat = (gcdStep u.toNat v.toNat).2 := by
  intro lt od
  have hu := u.isLt
  have hv := v.isLt
  unfold gcdStep
  by_cases ho : u.toNat % 2 = 1 <;> by_cases hl : u.toNat < v.toNat <;>
    simp only [od, lt, ho, hl, decide_true, decide_false, mask_true, mask_false, ↓reduceIte, BitVec.and_allOnes,
      xor_cancel_l, not_sub_allOnes, shr1_toNat, BitVec.xor_self, xor_z, z_xor, and_z, sub_z]
  all_goals refine ⟨?_, ?_⟩
  all_goals first
    | trivial
    | (simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero])
    | (simp only [BitVec.toNat_neg, BitVec.toNat_sub]; congr 1; try omega)

/-- `bgcdStep`: `gcdStep` on `x3` and `x13`, with `x7 = 0` and `x8` all ones. -/
theorem bgcdStep_ok (s : State) (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = mask true) :
    WP isa (.block bgcdStep) s fun t =>
      ((t.gpr .x3).toNat = (gcdStep (s.gpr .x3).toNat (s.gpr .x13).toNat).1 ∧
        (t.gpr .x13).toNat = (gcdStep (s.gpr .x3).toNat (s.gpr .x13).toNat).2 ∧ t.mem = s.mem) ∧
      Keep [.x3, .x4, .x5, .x6, .x10, .x13] s t := by
  refine WP.keep [.x3, .x4, .x5, .x6, .x10, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  brun [bgcdStep, h7, h8, one16, add_not_one, lt_sel, odd_mask']
  exact gstep_bv _ _

/-- The gcd's 128 steps, from `u = x3` and the odd `v = x13`: `gcd u v` in
`x13`. -/
theorem gcdLoop_ok {s : State} (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = mask true) (h9 : s.gpr .x9 = BitVec.ofNat 64 128)
    (hv : (s.gpr .x13).toNat % 2 = 1) :
    WP isa (countLoop .x9 bgcdStep) s fun t =>
      (t.gpr .x13).toNat = Nat.gcd (s.gpr .x3).toNat (s.gpr .x13).toNat ∧ t.mem = s.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x9, .x10, .x13] s t := by
  have hu := (s.gpr .x3).isLt
  have hvl := (s.gpr .x13).isLt
  refine WP.mono (wp_countdown (cnt := .x9) (N := 128) (by decide) (by decide)
    (fun i t => (t.gpr .x3).toNat = (gcdIter i (s.gpr .x3).toNat (s.gpr .x13).toNat).1 ∧
      (t.gpr .x13).toNat = (gcdIter i (s.gpr .x3).toNat (s.gpr .x13).toNat).2 ∧ t.mem = s.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x9, .x10, .x13] s t) ?_ ⟨rfl, rfl, rfl, Keep.refl _ _⟩ h9) fun t ⟨_, h13, hm, k⟩ => ?_
  · intro i _ t ⟨h3, h13, hm, k⟩ _
    refine WP.block_append_iff.mpr (WP.mono (bgcdStep_ok t ((k.gpr .x7 (by decide)).trans h7) ((k.gpr .x8 (by decide)).trans h8))
      fun t₁ ⟨⟨a, b, m₁⟩, k₁⟩ => ?_)
    refine WP.mono (dec_ok t₁ .x9) fun t' ⟨⟨h9', m', _⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, hm], ?_⟩, ?_⟩
    · rw [(k'.gpr .x3 (by decide)), a, h3, h13, gcdIter_succ']
    · rw [(k'.gpr .x13 (by decide)), b, h3, h13, gcdIter_succ']
    · exact ((k.trans k₁).trans k').mono (by decide)
    · rw [h9', k₁.gpr .x9 (by decide)]
  · refine ⟨?_, hm, k⟩
    rw [h13, gcdIter_eq 128 _ _ hv (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hu (Nat.le_of_lt hvl) (by omega))
      (by rw [← Nat.pow_add]))]

theorem zz_add (x : BitVec 64) : (0 : BitVec 64) + 0 + x = x := by simp

theorem zero_sub_mask (c : Bool) : (0 : BitVec 64) - BitVec.ofNat 64 c.toNat = mask c := by cases c <;> rfl

theorem ite_mask (c : Bool) : (if c = true then mask true else (0 : BitVec 64)) = mask c := by cases c <;> rfl

theorem mask_or2 (a b : Bool) : mask a ||| mask b = mask (a || b) := by cases a <;> cases b <;> decide

/-- One bit of `(c − 1) mod e` with masks, on words: `r' = 2 r + b` with its
carry, and `r' − e` kept if that carried or `r'` is not below `e`. -/
theorem modbit_bv (r e : BitVec 64) (b : Bool) (hre : r.toNat < e.toNat) :
    let r' := r + r + BitVec.ofNat 64 b.toNat
    (r' ^^^ ((r' - e ^^^ r') &&&
      ((if decide (2 ^ 64 ≤ r'.toNat + (~~~e).toNat + true.toNat) = true then mask true else 0) |||
        0 - BitVec.ofNat 64 (decide (2 ^ 64 ≤ r.toNat + r.toNat + b.toNat)).toNat))).toNat =
      (2 * r.toNat + b.toNat) % e.toNat := by
  intro r'
  have he := e.isLt
  have hrl := r.isLt
  have hbl : b.toNat ≤ 1 := by cases b <;> decide
  have hr' : r'.toNat = (r.toNat + r.toNat + b.toNat) % 2 ^ 64 := by
    simp only [r', BitVec.toNat_add, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]; omega
  have hne : (~~~e).toNat = 2 ^ 64 - 1 - e.toNat := by rw [BitVec.toNat_not]
  have hsub : e.toNat ≤ 2 * r.toNat + b.toNat → (2 * r.toNat + b.toNat) % e.toNat = 2 * r.toNat + b.toNat - e.toNat :=
    fun h => by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  rw [zero_sub_mask, ite_mask, mask_or2]
  generalize hg : (decide (2 ^ 64 ≤ r'.toNat + (~~~e).toNat + true.toNat) ||
    decide (2 ^ 64 ≤ r.toNat + r.toNat + b.toNat)) = g
  rw [hne, show true.toNat = 1 from rfl] at hg
  cases g
  · rw [mask_false, and_z, xor_z, hr', Nat.mod_eq_of_lt (by simp at hg; omega), Nat.mod_eq_of_lt]
    · omega
    · simp at hg; rw [hr'] at hg; omega
  · rw [mask_true, BitVec.and_allOnes, xor_cancel_l, BitVec.toNat_sub, hr']
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
    rw [hr'] at hg
    rw [hsub (by omega)]
    omega

/-- `modBit`: `r := (2 r + bit) mod e` for `r = x3 < e = x13` and the top bit
of `x2`, shifted out (`x7 = 0`, `x8` all ones). -/
theorem modBit_ok (s : State) (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = mask true)
    (hre : (s.gpr .x3).toNat < (s.gpr .x13).toNat) :
    WP isa (.block modBit) s fun t =>
      ((t.gpr .x3).toNat = (2 * (s.gpr .x3).toNat +
        (decide (2 ^ 64 ≤ (s.gpr .x2).toNat + (s.gpr .x2).toNat)).toNat) % (s.gpr .x13).toNat ∧
      t.gpr .x2 = s.gpr .x2 + s.gpr .x2 ∧ t.mem = s.mem) ∧ Keep [.x2, .x3, .x4, .x5, .x6] s t := by
  refine WP.keep [.x2, .x3, .x4, .x5, .x6] ?_ (by decide) (by decide) (by decide +kernel)
  brun [modBit, h7, h8, Bool.toNat_false, Nat.add_zero, zz_add, add_not_one]
  exact modbit_bv _ _ _ hre

end VG.Proof.RsaKeyGen.AArch64
