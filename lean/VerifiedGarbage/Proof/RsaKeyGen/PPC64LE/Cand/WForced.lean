module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Witness
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WUni
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Gcd
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: the forced witness

`forced_ok`: the draw `x` in array 4 copied to array 3, bit 1 set and the top
bit cleared: `(x | 2) mod 2^(64 w − 1)` (`wv_forced`), as
`RsaKeyGen.witness` forces a draw out of range.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (forced)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- Setting bit 1 of the low word and clearing the top bit of the top word of
a number of `w ≥ 2` words. -/
theorem wv_forced {m m' : Mem} {p : Addr} {d w : Nat} (hw : 2 ≤ w)
    (h0 : word m' p d = word m p d ||| BitVec.ofNat 64 2)
    (htop : word m' p (d + 8 * (w - 1)) = word m p (d + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ 63 - 1))
    (hmid : ∀ j, 0 < j → j < w - 1 → word m' p (d + 8 * j) = word m p (d + 8 * j)) :
    wv m' p d w = (wv m p d w ||| 2) % 2 ^ (64 * w - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
  by_cases hi : i < 64 * w
  · rw [VG.Proof.RsaKeyGen.testBit_wv m' p d w i hi, VG.Proof.RsaKeyGen.testBit_wv m p d w i hi]
    by_cases hj0 : i / 64 = 0
    · rw [hj0, Nat.mul_zero, Nat.add_zero, h0, BitVec.toNat_or, Nat.testBit_or, BitVec.toNat_ofNat,
        show i % 64 = i by omega, decide_eq_true (show i < 64 * w - 1 by omega)]
      simp
    · have h2 : Nat.testBit 2 i = false := by
        rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]; simp; omega
      rw [h2, Bool.or_false]
      by_cases hjt : i / 64 = w - 1
      · rw [hjt, htop, BitVec.toNat_and, Nat.testBit_and, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 2 ^ 63 - 1 < 2 ^ 64 by decide), Nat.testBit_two_pow_sub_one]
        by_cases h63 : i % 64 < 63
        · rw [decide_eq_true h63, decide_eq_true (show i < 64 * w - 1 by omega)]
          rw [show i % 64 = i - 64 * (w - 1) by omega]
          simp only [Bool.and_true, Bool.true_and]
        · rw [decide_eq_false h63, decide_eq_false (show ¬ i < 64 * w - 1 by omega)]
          simp
      · rw [hmid (i / 64) (by omega) (by omega), decide_eq_true (show i < 64 * w - 1 by omega)]
        simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega))),
      decide_eq_false (show ¬ i < 64 * w - 1 by omega)]
    simp

theorem mask63 : (BitVec.ofNat 64 0 - BitVec.ofNat 64 1) >>> 1 = BitVec.ofNat 64 (2 ^ 63 - 1) := by decide

/-- The registers `forced` writes. -/
def fdRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r14, .r15, .r17]

/-- `forced`: array 3 := `(x | 2) mod 2^(64 w − 1)` for the draw `x` in array
4, its word `w` zero. -/
theorem forced_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa forced s fun t =>
      (wv t.mem B (slot w 3) w = (wv s.mem B (slot w 4) w ||| 2) % 2 ^ (64 * w - 1) ∧
        word t.mem B (slot w 3 + 8 * w) = 0 ∧ VG.Proof.Mont.Outside B (slot w 3) (8 * w + 8) s.mem t.mem ∧
        Env t B Z w) ∧ Keep fdRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  rw [slot_lin] at hZ
  unfold forced
  refine WP.seq (WP.mono (toThree_ok h) fun t₁ ⟨⟨c3, z3, o₁, e₁⟩, k₁⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (e₁.base (rd := .r5) (by decide) (by decide) 3) fun t₂ ⟨⟨a5, m₂⟩, k₂⟩ => ?_
  have e₂ := e₁.keep k₂ (by decide)
  have e8 : off B (slot w 3) + BitVec.ofNat 64 (2 * w) <<< 2 - BitVec.ofNat 64 8 = off B (slot w 3 + 8 * (w - 1)) := by
    rw [show BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega, off_add, Offset.add_ofNat_sub _ (show 8 ≤ slot w 3 + 8 * w by omega),
      show slot w 3 + 8 * w - 8 = slot w 3 + 8 * (w - 1) by omega]
  have sep : ∀ (m : Mem) (x : BitVec 64), (m.writeW (off B (slot w 3)) x).readW (off B (slot w 3 + 8 * (w - 1))) 64 =
      m.readW (off B (slot w 3 + 8 * (w - 1))) 64 := fun m x =>
    Mem.readW_writeW_sep (Offset.sep B (by omega) (by rw [slot_lin]; omega) (by rw [slot_lin]; omega)) (by decide)
  refine WP.mono (WP.keep [.r3, .r4, .r5, .r6] (Q := fun t => t.mem =
      (t₂.mem.writeW (off B (slot w 3)) (word t₂.mem B (slot w 3) ||| BitVec.ofNat 64 2)).writeW
        (off B (slot w 3 + 8 * (w - 1))) (word t₂.mem B (slot w 3 + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ 63 - 1)))
    (by
      prun [a5, e₂.h11, e8, mask63, sep, e₂.hs.ld (d := slot w 3) (n := 8) (by rw [slot_lin]; omega),
        e₂.hs.st (d := slot w 3) (n := 8) (by rw [slot_lin]; omega),
        e₂.hs.ld (d := slot w 3 + 8 * (w - 1)) (n := 8) (by rw [slot_lin]; omega),
        e₂.hs.st (d := slot w 3 + 8 * (w - 1)) (n := 8) (by rw [slot_lin]; omega)]
      done)
    (by decide)) fun t ⟨tm, kt⟩ => ?_
  have K := (k₁.trans k₂).trans kt
  have rd : ∀ d e : Nat, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ Z → e + 8 ≤ Z → ∀ (m : Mem) (x : BitVec 64),
      word (m.writeW (off B e) x) B d = word m B d := fun d e h1 h2 h3 m x =>
    Mem.readW_writeW_sep (Offset.sep B h1 (by omega) (by omega)) (by decide)
  have hb3 : slot w 3 + 8 * w + 8 ≤ Z := by rw [slot_lin]; omega
  have hx : wv t₂.mem B (slot w 3) w = wv s.mem B (slot w 4) w := by
    rw [m₂]; exact wv_shift' fun i hi => c3 i hi
  refine ⟨⟨?_, ?_, ?_, e₂.keep kt (by decide)⟩, K.mono (by simp [fdRegs])⟩
  · rw [← hx]
    refine wv_forced (by omega) ?_ ?_ ?_
    · rw [tm, rd _ _ (by omega) (by omega) (by omega), word_writeW_self]
    · rw [tm, word_writeW_self]
    · intro j h1 h2
      rw [tm, rd _ _ (by omega) (by omega) (by omega), rd _ _ (by omega) (by omega) (by omega)]
  · rw [tm, rd _ _ (by omega) (by omega) (by omega), rd _ _ (by omega) (by omega) (by omega), m₂]; exact z3
  · rw [tm]
    have w1 := VG.Proof.Mont.writeW_outside t₂.mem B (d := slot w 3) (word t₂.mem B (slot w 3) ||| BitVec.ofNat 64 2)
      (by omega)
    have w2 := VG.Proof.Mont.writeW_outside (t₂.mem.writeW (off B (slot w 3)) (word t₂.mem B (slot w 3) |||
      BitVec.ofNat 64 2)) B (d := slot w 3 + 8 * (w - 1))
      (word t₂.mem B (slot w 3 + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ 63 - 1)) (by omega)
    rw [m₂] at w1 w2 ⊢
    exact (o₁.trans (w1.mono (by omega) (by omega))).trans (w2.mono (by omega) (by omega))

end VG.Proof.RsaKeyGen.PPC64LE.Cand
