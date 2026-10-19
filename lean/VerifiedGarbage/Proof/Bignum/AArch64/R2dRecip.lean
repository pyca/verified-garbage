module
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `R² mod m` by long division on AArch64: the reciprocal

`divBit` is a bit of restoring division: the remainder `r < d` becomes
`2 r + 1` less `d` if that is at least `d`, and the quotient `q` becomes
`2 q` plus that bit (`r2dDivBit_ok`). `recip` divides
`(2^64 - 1 - d) 2^64 + 2^64 - 1` by `d` that way, 64 bits, to
`v = ⌊(2^128 - 1) / d⌋ - 2^64` (`r2dRecip_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `2 r + 1` modulo `2^64`, as `divBit` computes it. -/
def dbS (r : BitVec 64) : BitVec 64 := r <<< 1 ||| 1#64

/-- The bit of the quotient: the carry out of `2 r + 1`, or `2 r + 1 ≥ d`. -/
def dbB (r d : BitVec 64) : BitVec 64 :=
  (0 : BitVec 64) + (0 : BitVec 64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ (dbS r).toNat + (~~~d).toNat + (true : Bool).toNat)).toNat |||
    r >>> 63

/-- The remainder. -/
def dbR (r d : BitVec 64) : BitVec 64 :=
  if (!decide ((dbB r d &&& dbB r d) = 0)) = true then dbS r + ~~~d + BitVec.ofNat 64 (true : Bool).toNat
  else dbS r

theorem dbS_toNat (r : BitVec 64) : (dbS r).toNat = (2 * r.toNat + 1) % 2 ^ 64 := by
  have h : r <<< 1 &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_shiftLeft, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod,
      Nat.shiftLeft_eq, Nat.pow_one, show (0#64).toNat = 0 from rfl]
    omega
  rw [dbS, ← BitVec.add_eq_or_of_and_eq_zero _ _ h, BitVec.toNat_add, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq, Nat.pow_one, BitVec.toNat_ofNat]
  omega

theorem shr63_toNat (r : BitVec 64) : (r >>> 63) = BitVec.ofNat 64 (decide (2 ^ 63 ≤ r.toNat)).toNat := by
  have := r.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 63 ≤ r.toNat <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega

theorem zero_zero_add (x : BitVec 64) : (0 : BitVec 64) + 0 + x = x := by simp

theorem or_bits (a b : Bool) :
    BitVec.ofNat 64 a.toNat ||| BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 (a || b).toNat := by
  cases a <;> cases b <;> rfl

theorem dbB_val {r d : Nat} (hr : r < d) (hd : d < 2 ^ 64) :
    dbB (BitVec.ofNat 64 r) (BitVec.ofNat 64 d) = BitVec.ofNat 64 (decide (d ≤ 2 * r + 1)).toNat := by
  have hR : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  rw [dbB, not_carry, dbS_toNat, shr63_toNat, hR, hD, zero_zero_add, or_bits]
  congr 2
  by_cases h : 2 ^ 63 ≤ r
  · simp only [h, decide_true, Bool.or_true]
    symm; apply decide_eq_true; omega
  · simp only [h, decide_false, Bool.or_false]
    apply decide_eq_decide.mpr
    rw [Nat.mod_eq_of_lt (by omega)]

theorem dbR_val {r d : Nat} (hr : r < d) (hd : d < 2 ^ 64) :
    dbR (BitVec.ofNat 64 r) (BitVec.ofNat 64 d) =
      BitVec.ofNat 64 (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) := by
  have hR : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hD : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  rw [dbR, dbB_val hr hd, BitVec.and_self]
  apply BitVec.eq_of_toNat_eq
  by_cases h : d ≤ 2 * r + 1
  · rw [decide_eq_true h, ite_eq_left (by rfl)]
    rw [ite_eq_left h, BitVec.toNat_add, BitVec.toNat_add, dbS_toNat, BitVec.toNat_not, hR, hD, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Bool.toNat_true]
    omega
  · rw [decide_eq_false h, ite_eq_right (by decide), ite_eq_right h, dbS_toNat, hR, BitVec.toNat_ofNat]

/-! ## The loop -/

/-- After `k` bits of `recip`'s loop from `s₀`: `x2 = r`, `x10 = q` for
`r₀ 2^k + 2^k - 1 = q d + r`, `r < d`. -/
structure R2dRecInv (s₀ : State) (d r0 : Nat) (k : Nat) (t : State) : Prop where
  keep : Keep [.x2, .x3, .x10, .x13, .x15, .x16] s₀ t
  mem : t.mem = s₀.mem
  val : ∃ q r, t.gpr .x2 = BitVec.ofNat 64 r ∧ t.gpr .x10 = BitVec.ofNat 64 q ∧
    r0 * 2 ^ k + (2 ^ k - 1) = q * d + r ∧ r < d

theorem r2dDivBit_ok (t : State) (h4 : t.gpr .x4 = (BitVec.ofNat 16 1).setWidth 64) (h7 : t.gpr .x7 = 0) :
    WP isa (.block divBit) t fun t' => (t'.gpr .x2 = dbR (t.gpr .x2) (t.gpr .x5) ∧
      t'.gpr .x10 = t.gpr .x10 + t.gpr .x10 + dbB (t.gpr .x2) (t.gpr .x5) ∧ t'.mem = t.mem) ∧
      Keep [.x2, .x3, .x10, .x15, .x16] t t' := by
  refine WP.keep [.x2, .x3, .x10, .x15, .x16] ?_ (by decide) rfl (by decide +kernel)
  brun [divBit, h4, h7, r2d_exec_tst, r2d_exec_cselc, CondCode.holds]
  exact ⟨rfl, rfl⟩

theorem divStep_ok {s₀ : State} {d r0 : Nat} (hd : d < 2 ^ 64) (hr0 : r0 < d)
    (h4 : s₀.gpr .x4 = (BitVec.ofNat 16 1).setWidth 64) (h7 : s₀.gpr .x7 = 0)
    (h5 : s₀.gpr .x5 = BitVec.ofNat 64 d) {k : Nat} (hk : k < 64) {t : State} (hI : R2dRecInv s₀ d r0 k t) :
    WP isa (.block (divBit ++ ([.subImm .x .x13 .x13 1] : List Instr))) t fun t' =>
      R2dRecInv s₀ d r0 (k + 1) t' ∧ t'.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  obtain ⟨q, r, h2, h10, hP, hr⟩ := hI.val
  have t4 := (hI.keep.gpr .x4 (by decide)).trans h4
  have t7 := (hI.keep.gpr .x7 (by decide)).trans h7
  have t5 := (hI.keep.gpr .x5 (by decide)).trans h5
  rw [WP.block_append_iff]
  refine WP.mono (r2dDivBit_ok t t4 t7) fun t₁ ⟨⟨h2₁, h10₁, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x13) fun t' ⟨⟨h13, hm', _⟩, k'⟩ => ⟨?_, by rw [h13, k₁.gpr .x13 (by decide)]⟩
  -- `q < 2^k`, as `q d ≤ r₀ 2^k + 2^k - 1 < d 2^k`.
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hq : q < 2 ^ k := by
    have h1 : q * d < 2 ^ k * d := by
      have := Nat.mul_le_mul_left (2 ^ k) (show r0 + 1 ≤ d by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      rw [Nat.mul_comm r0] at hP
      omega
    exact Nat.lt_of_mul_lt_mul_right h1
  have hk' : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨hP', hr'⟩ := WordStep.divBit_inv (P := r0 * 2 ^ k + (2 ^ k - 1)) (q := q) (r := r)
    (d := d) hP hr (b := 1) (by decide)
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), by rw [hm', hm₁, hI.mem], ?_⟩
  refine ⟨2 * q + (if d ≤ 2 * r + 1 then 1 else 0), if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1,
    by rw [k'.gpr .x2 (by decide), h2₁, h2, t5, dbR_val hr hd],
    ?_, ?_, hr'⟩
  · rw [k'.gpr .x10 (by decide), h10₁, h2, t5, h10, dbB_val hr hd]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : 2 * q + 1 < 2 ^ 64 := by omega
    by_cases h : d ≤ 2 * r + 1 <;> simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false,
      ↓reduceIte] <;> omega
  · rw [Nat.pow_succ]
    have e : r0 * (2 ^ k * 2) + (2 ^ k * 2 - 1) = 2 * (r0 * 2 ^ k + (2 ^ k - 1)) + 1 := by
      have := Nat.two_pow_pos k; rw [← Nat.mul_assoc, Nat.mul_add, Nat.mul_comm 2 (r0 * 2 ^ k)]; omega
    rw [e, hP']

/-- `recip`: `v = ⌊(2^128 - 1) / d⌋ - 2^64` for `d = m[w - 1] ≥ 2^63` into the
word at `x6`, for `m` at `x9` of `w` words. -/
theorem r2dRecip_ok {s : State} {B : Addr} {Z w eM eV : Nat} (hs : Scr s B Z)
    (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h6 : s.gpr .x6 = off B eV)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hM : eM + 8 * w ≤ Z) (hV : eV + 8 ≤ Z)
    (hd : 2 ^ 63 ≤ (word s.mem B (eM + 8 * (w - 1))).toNat) :
    WP isa recip s fun t =>
      (word t.mem B eV).toNat = (2 ^ 128 - 1) / (word s.mem B (eM + 8 * (w - 1))).toNat - 2 ^ 64 ∧
      Outside B eV 8 s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x5, .x10, .x13, .x15, .x16] s t := by
  have hn := hs.nowrap
  generalize hD : word s.mem B (eM + 8 * (w - 1)) = D at hd
  have hD' := D.isLt
  have hsub : (0 : BitVec 64) - D - BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ 64 - 1 - D.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]
    omega
  unfold recip
  refine WP.seq (WP.mono (WP.keep [.x2, .x4, .x5, .x10, .x13] (Q := fun t =>
    t.gpr .x5 = BitVec.ofNat 64 D.toNat ∧ t.gpr .x2 = BitVec.ofNat 64 (2 ^ 64 - 1 - D.toNat) ∧
    t.gpr .x10 = BitVec.ofNat 64 0 ∧ t.gpr .x4 = (BitVec.ofNat 16 1).setWidth 64 ∧
    t.gpr .x13 = BitVec.ofNat 64 64 ∧ t.mem = s.mem)
    (by brun [h9, h12, h7, shl3_sub8 hw (show w < 2 ^ 61 by omega), off_add,
        hs.ld (show eM + 8 * (w - 1) + 8 ≤ Z by omega), hD, hsub]
        <;> first | rfl | rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h5, h2, h10, h4, h13, hm₁⟩, k₁⟩ => ?_)
  have hr0 : 2 ^ 64 - 1 - D.toNat < D.toNat := by omega
  have h0 : R2dRecInv s₁ D.toNat (2 ^ 64 - 1 - D.toNat) 0 s₁ :=
    ⟨Keep.refl _ _, rfl, 0, 2 ^ 64 - 1 - D.toNat, h2, h10, by simp, hr0⟩
  refine WP.seq (WP.mono (wp_countdown (N := 64) (by decide) (by decide) (R2dRecInv s₁ D.toNat (2 ^ 64 - 1 - D.toNat))
    (fun k hk t hI _ => divStep_ok hD' hr0 h4 ((k₁.gpr .x7 (by decide)).trans h7) h5 hk hI) h0 h13)
    fun t hI => ?_)
  obtain ⟨q, r, _, h10t, hP, hr⟩ := hI.val
  have t6 : t.gpr .x6 = off B eV := (hI.keep.gpr .x6 (by decide)).trans ((k₁.gpr .x6 (by decide)).trans h6)
  have hst : InRegions t.wr (off B eV) 8 := by
    rw [hI.keep.wr, k₁.wr]; exact hs.st (by omega)
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B eV) (t.gpr .x10))
    (by brun [t6, hst]) (by decide) (by decide) (by decide +kernel)) fun t' ⟨hm', k'⟩ => ?_
  have hq : q = (2 ^ 128 - 1) / D.toNat - 2 ^ 64 := by
    rw [← WordStep.recip_eq hD' (by omega), hP, Nat.mul_comm q, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr,
      Nat.add_zero]
  have hqB : q < 2 ^ 64 := by
    rw [hq]
    have : (2 ^ 128 - 1) / D.toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have := Nat.mul_le_mul_left (2 ^ 65) hd
      omega
    omega
  refine ⟨by rw [hm', word_writeW_self, h10t, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, hq], ?_,
    ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  rw [hm', hI.mem, hm₁]
  exact writeW_outside _ _ _ (by omega)

end VG.Proof.Bignum.AArch64
