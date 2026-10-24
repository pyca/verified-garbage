module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: masking the key

`maskWords_ok`: `w` words `&=` the mask. `orThree_ok`: an array kept under
the mask, else 3.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `maskWords`, `r14` at offset `d` of `B`: the `w` words there `&= r26`. -/
theorem maskWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B d) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : d + 8 * w ≤ Z) :
    WP isa maskWords s fun t =>
      ((∀ i < w, word t.mem B (d + 8 * i) = word s.mem B (d + 8 * i) &&& s.gpr .r26) ∧
        Outside B d (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r17] s t := by
  have hnw := hs.nowrap
  unfold maskWords
  refine WP.seq ?_
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1]) s fun s₁ =>
      (s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  refine WP.mono hpre fun s₁ ⟨⟨i17, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (d + 8 * i) ∧ Outside B d (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (d + 8 * k) = word s.mem B (d + 8 * k) &&& s.gpr .r26) ∧
      Keep [.r0, .r14, .r17] s t
  refine WP.mono (wp_countdown (cnt := .r17) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j14, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr .r14 (by decide), h14]; rfl, by rw [im]; exact Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega), k₁.mono⟩ i17) fun t ⟨_, tout, tz, tk⟩ => ⟨⟨tz, tout⟩, tk⟩
  have h26 : t.gpr .r26 = s.gpr .r26 := jk.gpr _ (by decide)
  refine WP.mono (WP.keep [.r0, .r14, .r17] (Q := fun t' =>
    t'.mem = t.mem.writeW (off B (d + 8 * i)) (word t.mem B (d + 8 * i) &&& s.gpr .r26) ∧
      t'.gpr .r14 = off B (d + 8 * (i + 1)) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) ?_ (by decide))
    fun t' ⟨⟨a, b, c⟩, k⟩ => ⟨⟨b, ?_, ?_, jk.trans' k⟩, c⟩
  · prun [j14, h26, (hs.congr jk.wr).ld (show d + 8 * i + 8 ≤ Z by omega),
      (hs.congr jk.wr).st (show d + 8 * i + 8 ≤ Z by omega)]
    simp only [Mont.off, off]; congr 2
  · have hw := writeW_outside t.mem B (d := d + 8 * i) (word t.mem B (d + 8 * i) &&& s.gpr .r26) (by omega)
    rw [a]; exact (jout.mono (Nat.le_refl _) (by omega)).trans (hw.mono (by omega) (by omega))
  · intro k hk
    have hw := writeW_outside t.mem B (d := d + 8 * i) (word t.mem B (d + 8 * i) &&& s.gpr .r26) (by omega)
    rw [a]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega) (by omega)]; exact jz k hk
    · rw [word_writeW_self, jout.word (Or.inr (Nat.le_refl _)) (by omega)]

/-- The mask of `b`, on a word. -/
theorem and_mask (x : BitVec 64) (b : Bool) :
    x &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) = if b then x else 0 := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact BitVec.and_zero
  · simp only [↓reduceIte]; exact BitVec.and_allOnes

theorem three_mask (x : BitVec 64) (b : Bool) :
    x ||| (((0#64 - 1#64) ^^^ (0#64 - BitVec.ofNat 64 (if b then 1 else 0))) &&& 3#64) =
      x ||| (if b then 0 else 3) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> congr 1

/-- `orThree j`, the mask of `b` in `r26`: array `j` (`w` words) kept if `b`,
else 3. -/
theorem orThree_ok {s : State} {B : Addr} {Z w j : Nat} {b : Bool} (hs : Scr s B Z) (hj : j < 8)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) :
    WP isa (orThree j) s fun t =>
      (Mont.val32 t.mem B (slot w j) (2 * w) = (if b then Mont.val32 s.mem B (slot w j) (2 * w) else 3) ∧
        Outside B (slot w j) (8 * w) s.mem t.mem) ∧ Keep [.r0, .r3, .r4, .r14, .r17] s t := by
  have hnw := hs.nowrap
  have sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_le hj) hZ
  unfold orThree
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 j)
    fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (maskWords_ok (hs.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans h11) hw hw'
    (by omega)) fun s₂ ⟨⟨hm, out₂⟩, k₂⟩ => ?_)
  have k12 := k1.trans k₂
  rw [m1, k1.gpr .r26 (by decide), h26] at hm
  rw [m1] at out₂
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) j) fun s₃ ⟨⟨b14, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (WP.keep [.r0, .r3, .r4] (Q := fun t => t.mem = s₃.mem.writeW (off B (slot w j))
    (word s₃.mem B (slot w j) ||| (if b then 0 else 3))) ?_ (by decide)) fun t ⟨tm, k4⟩ =>
    ⟨⟨?_, ?_⟩, (k13.trans k4).mono⟩
  · prun [b14, BitVec.add_zero, (k13.gpr .r26 (by decide)).trans h26, (hs.congr k13.wr).ld (show slot w j + 8 ≤ Z by omega),
      (hs.congr k13.wr).st (show slot w j + 8 ≤ Z by omega), three_mask]
  · rw [m3] at tm
    have ow := writeW_outside s₂.mem B (d := slot w j) (word s₂.mem B (slot w j) ||| (if b then 0 else 3))
      (by omega)
    have hm0 := hm 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at hm0
    rw [Pre.val32_eq_wv, Pre.val32_eq_wv]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [wv_single (i := 0) _ _ _ w (by omega) fun q hq hne => ?_]
      · rw [tm, Nat.mul_zero, Nat.add_zero, word_writeW_self, hm0, and_mask]
        simp
      · rw [tm, ow.word (by omega) (by omega), hm q hq, and_mask]; rfl
    · simp only [↓reduceIte]
      refine wv_congr fun q hq => ?_
      rcases Nat.eq_zero_or_pos q with rfl | hq0
      · rw [tm, Nat.mul_zero, Nat.add_zero, word_writeW_self, hm0, and_mask]
        simp
      · rw [tm, ow.word (by omega) (by omega), hm q hq, and_mask]; rfl
  · rw [m3] at tm
    rw [tm]
    exact out₂.trans ((writeW_outside s₂.mem B (d := slot w j) _ (by omega)).mono (Nat.le_refl _) (by omega))

end VG.Proof.Bignum.PPC64LE.Crt
