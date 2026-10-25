module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Digit
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaKeyGen.Trial64
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Trial division on PPC64LE: one table entry

`digits_ok`: the `w` words of the candidate `c` reduced into `acc`, with
`acc < 2 s` and `acc 2^(64 w) ≡ c (mod s)` (`trial_word64`, from the words
up). `entry_ok`: the entry `i` of the table at `r23`, its flag of dividing
`c` in `r22` (`trial_div`), `r23` at the next entry, and `r24` counted down,
or cleared on a hit.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Trial

open VG VG.PPC64LE VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.PPC64LE.Trial VG.Proof.Bignum.PPC64LE VG.Proof.Mont
open VG.Impl.Bignum.PPC64LE (countLoop)

/-- The `w` words at `o` (from `r10`) into `acc` (`r3`), counted by `r4`. -/
theorem digits_ok {u : State} {B : Addr} {Z o w s : Nat} {m : BitVec 64} (hs : Scr u B Z)
    (h5 : u.gpr .r5 = off B o) (h3 : u.gpr .r3 = BitVec.ofNat 64 0) (h4 : u.gpr .r4 = BitVec.ofNat 64 w)
    (h8 : u.gpr .r8 = BitVec.ofNat 64 s) (h9 : u.gpr .r9 = m) (hs2 : 2 ≤ s) (hs' : s < 2 ^ 14)
    (hinv : (s * m.toNat + 1) % 2 ^ 64 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) :
    WP isa (countLoop .r4 digit) u fun t =>
      ((∃ acc, t.gpr .r3 = BitVec.ofNat 64 acc ∧ acc < 2 * s ∧
        acc * 2 ^ (64 * w) % s = val32 u.mem B o (2 * w) % s) ∧ t.mem = u.mem) ∧ Keep (.r4 :: digitRegs) u t := by
  let Inv : Nat → State → Prop := fun j t =>
    ((∃ acc, t.gpr .r3 = BitVec.ofNat 64 acc ∧ acc < 2 * s ∧ acc * 2 ^ (64 * j) % s = wordsVal u.mem B o j % s) ∧
      t.gpr .r5 = off B (o + 8 * j) ∧ t.mem = u.mem) ∧ Keep (.r4 :: digitRegs) u t
  refine WP.mono (wp_countdown (cnt := .r4) (N := w) (by omega) (by omega) Inv
    (fun j hj t ⟨⟨⟨acc, t3, hacc, hv⟩, t5, tm⟩, kt⟩ _ => ?_)
    ⟨⟨⟨0, h3, by omega, by simp [wordsVal]⟩, by rw [h5, Nat.mul_zero, Nat.add_zero], rfl⟩, Keep.refl _ _⟩ h4)
    fun t ⟨⟨⟨acc, t3, hacc, hv⟩, _, tm⟩, kt⟩ => ⟨⟨⟨acc, t3, hacc, by rw [hv, wordsVal_eq_val32]⟩, tm⟩, kt⟩
  rw [WP.block_append_iff]
  have ht : Scr t B Z := hs.congr kt.wr
  refine WP.mono (digit_ok ht t5 t3 ((kt.gpr .r8 (by decide)).trans h8) ((kt.gpr .r9 (by decide)).trans h9) hacc hs2
    hs' hinv (by omega)) fun t₁ ⟨⟨⟨r, a3, hr, hrv⟩, a5, am⟩, k1⟩ => ?_
  refine WP.mono (subi_ok t₁ .r4 (by decide)) fun t₂ e => ?_
  subst e
  refine ⟨⟨⟨⟨r, by simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact a3, hr, ?_⟩,
    by simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact a5, by rw [mem_write, am, tm]⟩,
    (kt.trans (k1.trans (Keep.write _ _ _))).mono (by decide)⟩, ?_⟩
  · rw [VG.Proof.RsaKeyGen.trial_word64 hrv hv, wordsVal_succ_top, tm, Nat.add_comm (wordsVal _ _ _ _)]
  · simp only [gpr_write, ↓reduceIte]
    rw [k1.gpr .r4 (by decide)]

/-- `(x − 1) >> 63` is 1 for `x = 0`, and 0 for any other `x < 2^63`. -/
theorem zero_flag {x : Nat} (hx : x < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 (if x = 0 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> omega

theorem xor_zero_iff {a b : Nat} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (a ^^^ ·) h
    simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at this
    exact this.symm
  · rintro rfl; exact Nat.xor_self a

/-- `((a ^ b) − 1) >> 63` is 1 for `a = b`, else 0. -/
theorem eq_flag {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b) - BitVec.ofNat 64 1) >>> 63 =
      BitVec.ofNat 64 (if a = b then 1 else 0) := by
  have exs : BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = BitVec.ofNat 64 (a ^^^ b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (show a < 2 ^ 64 by omega) (show b < 2 ^ 64 by omega))]
  rw [exs, zero_flag (Nat.xor_lt_two_pow ha hb)]
  simp only [xor_zero_iff]

/-- `(n − 1) & (f − 1)`: 0 for the flag `f = 1`, `n − 1` for `f = 0`. -/
theorem count_flag {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 64) (b : Bool) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1) &&& (BitVec.ofNat 64 (if b then 1 else 0) - BitVec.ofNat 64 1) =
      BitVec.ofNat 64 (if b then 0 else n - 1) := by
  apply BitVec.eq_of_toNat_eq
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn',
      show (2 ^ 64 - 1 % 2 ^ 64 + 0 % 2 ^ 64) % 2 ^ 64 = 2 ^ 64 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod, Nat.mod_eq_of_lt (show n - 1 < 2 ^ 64 by omega)]
    omega
  · simp only [↓reduceIte]
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    simp

/-- The registers `entry` writes. -/
def entryRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r22, .r23, .r24]

/-- The entry `i` at `T` (`r23`): `r22 :=` its flag of dividing `c`, `r23 :=`
the next entry, `r24 :=` 0 on a hit, else one less. -/
theorem entry_ok {u : State} {B T : Addr} {Z o w c i n : Nat} (hs : Scr u B Z)
    (h10 : u.gpr .r10 = off B o) (h11 : u.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hc : val32 u.mem B o (2 * w) = c) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (hi : i < 1024)
    (h23 : u.gpr .r23 = T) (hT : u.mem.readW T 64 = BitVec.ofNat 64 (TrialTable32.entry i))
    (hTr : InRegions (u.rd ++ u.wr) T 8) (h24 : u.gpr .r24 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) :
    WP isa entry u fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if c % tabEntry i = 0 then 1 else 0) ∧ t.gpr .r23 = T + BitVec.ofNat 64 8 ∧
        t.gpr .r24 = BitVec.ofNat 64 (if c % tabEntry i = 0 then 0 else n - 1) ∧ t.mem = u.mem) ∧
        Keep entryRegs u t := by
  obtain ⟨hodd, h3, h8162⟩ := VG.Proof.RsaKeyGen.tabEntry_facts hi
  have hinv := VG.Proof.RsaKeyGen.TrialTable32.inverse_entry hi
  have hlo := VG.Proof.RsaKeyGen.TrialTable32.entry_low hi
  have hhi := VG.Proof.RsaKeyGen.TrialTable32.entry_high hi
  have heb := VG.Proof.RsaKeyGen.TrialTable32.entry_bound hi
  have hsv := (TrialTable32.inverse (BitVec.ofNat 32 (tabEntry i))).isLt
  generalize tabEntry i = s at hodd h3 h8162 hinv hlo hhi hsv ⊢
  generalize (TrialTable32.inverse (BitVec.ofNat 32 s)).toNat = sv at hinv hhi hsv
  have e8 : BitVec.ofNat 64 (TrialTable32.entry i) <<< 32 >>> 32 = BitVec.ofNat 64 s := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt heb,
      show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right,
      Nat.mul_div_cancel _ (Nat.two_pow_pos 32), hlo, Nat.mod_eq_of_lt (by omega)]
  have e9 : BitVec.ofNat 64 (TrialTable32.entry i) >>> 32 = BitVec.ofNat 64 sv := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt heb, hhi, Nat.mod_eq_of_lt (by omega)]
  -- `−s⁻¹ mod 2⁶⁴` by a step of Newton's iteration.
  have hinv64 : (s * ((BitVec.ofNat 64 s * BitVec.ofNat 64 sv + BitVec.ofNat 64 2) * BitVec.ofNat 64 sv).toNat + 1) %
      2 ^ 64 = 0 := by
    have h := mont_newton64 (BitVec.ofNat 64 s) (BitVec.ofNat 64 sv) (by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show sv < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show s < 2 ^ 32 by omega)]
      exact hinv)
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega)] at h
  unfold entry
  refine WP.seq (WP.mono (WP.keep [.r3, .r4, .r5, .r6, .r8, .r9] (Q := fun v => v.gpr .r8 = BitVec.ofNat 64 s ∧
      v.gpr .r9 = (BitVec.ofNat 64 s * BitVec.ofNat 64 sv + BitVec.ofNat 64 2) * BitVec.ofNat 64 sv ∧
      v.gpr .r3 = BitVec.ofNat 64 0 ∧ v.gpr .r5 = off B o ∧
      v.gpr .r4 = BitVec.ofNat 64 w ∧ v.mem = u.mem) ?_ (by decide)) fun v ⟨⟨v8, v9, v3, v5, v4, vm⟩, kv⟩ => ?_)
  · simp only [load]
    prun [h23, hT, hTr, h10, h11, BitVec.add_zero, e8, e9, mont_ofNat_shr1 (show w < 2 ^ 63 by omega)]
  have hv' : Scr v B Z := hs.congr kv.wr
  refine WP.seq (WP.mono (digits_ok hv' v5 v3 v4 v8 v9 (by omega) (by omega) hinv64 hw hw' hZ)
    fun x ⟨⟨⟨acc, x3, hacc, hacv⟩, xm⟩, kx⟩ => ?_)
  rw [vm, hc] at hacv
  have key : c % s = 0 ↔ acc = 0 ∨ acc = s := VG.Proof.RsaKeyGen.trial_div hodd hacc hacv
  have x8 : x.gpr .r8 = BitVec.ofNat 64 s := (kx.gpr .r8 (by decide)).trans v8
  have x23 : x.gpr .r23 = T := (kx.gpr .r23 (by decide)).trans ((kv.gpr .r23 (by decide)).trans h23)
  have x24 : x.gpr .r24 = BitVec.ofNat 64 n := (kx.gpr .r24 (by decide)).trans ((kv.gpr .r24 (by decide)).trans h24)
  refine WP.mono (WP.keep [.r6, .r7, .r22, .r23, .r24] (Q := fun y =>
      y.gpr .r22 = BitVec.ofNat 64 (if c % s = 0 then 1 else 0) ∧ y.gpr .r23 = T + BitVec.ofNat 64 8 ∧
        y.gpr .r24 = BitVec.ofNat 64 (if c % s = 0 then 0 else n - 1) ∧ y.mem = x.mem) ?_ (by decide))
    fun y ⟨⟨y22, y23, y24, ym⟩, ky⟩ => ⟨⟨y22, y23, y24, by rw [ym, xm, vm]⟩,
      ((kv.trans kx).trans ky).mono (by decide)⟩
  simp only [finish]
  prun [x3, x8, x23, x24, zero_flag (show acc < 2 ^ 63 by omega), eq_flag (show acc < 2 ^ 63 by omega)
    (show s < 2 ^ 63 by omega)]
  have hf : (BitVec.ofNat 64 (if acc = 0 then 1 else 0) ||| BitVec.ofNat 64 (if acc = s then 1 else 0)) =
      BitVec.ofNat 64 (if decide (c % s = 0) then 1 else 0) := by
    by_cases a0 : acc = 0
    · have hd : decide (c % s = 0) = true := decide_eq_true (key.mpr (Or.inl a0))
      have a1 : ¬ (0 = s) := by omega
      simp only [a0, a1, hd, ↓reduceIte]
      decide
    · by_cases a1 : acc = s
      · have hd : decide (c % s = 0) = true := decide_eq_true (key.mpr (Or.inr a1))
        have s0 : ¬ (s = 0) := by omega
        simp only [a1, s0, hd, ↓reduceIte]
        decide
      · have hd : decide (c % s = 0) = false := decide_eq_false (fun h => (key.mp h).elim a0 a1)
        simp only [a0, a1, hd, ↓reduceIte, Bool.false_eq_true]
        decide
  rw [hf, count_flag hn (by omega)]
  by_cases hit : c % s = 0 <;> simp [hit]

end VG.Proof.RsaKeyGen.PPC64LE.Trial
