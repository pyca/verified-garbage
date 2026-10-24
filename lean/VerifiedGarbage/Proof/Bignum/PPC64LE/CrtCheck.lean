module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: the checks

`checkN_ok`: the mask of whether `n` is valid. `checkLt_ok`: the mask of
whether one array is below another, and-ed in.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- Whether a word is zero, as a bit. -/
theorem isZero_bits (v : BitVec 64) :
    (((v >>> 1) ||| (v &&& 1#64)) - 1#64) >>> 63 = BitVec.ofNat 64 (if v = 0 then 1 else 0) := by
  by_cases h : v.toNat ≤ 1
  · rcases (show v = 0 ∨ v = 1 by
      rcases (show v.toNat = 0 ∨ v.toNat = 1 by omega) with h | h
      · exact Or.inl (BitVec.eq_of_toNat_eq h)
      · exact Or.inr (BitVec.eq_of_toNat_eq h)) with rfl | rfl <;> decide
  · have hu1 : 1 ≤ ((v >>> 1) ||| (v &&& 1#64)).toNat := by
      have := Nat.left_le_or (n := (v >>> 1).toNat) (m := (v &&& 1#64).toNat)
      rw [BitVec.toNat_or]
      have : (v >>> 1).toNat = v.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have hu2 : ((v >>> 1) ||| (v &&& 1#64)).toNat < 2 ^ 63 := by
      rw [BitVec.toNat_or]
      apply Nat.or_lt_two_pow
      · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := v.isLt; omega
      · rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hv : v ≠ 0 := fun e => by subst e; simp at h
    simp only [hv, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega

/-- `checkN`: `r26 :=` all ones if the `k` bytes of `n` (at `N`, from the
header) are a valid modulus, else 0. -/
theorem checkN_ok {s : State} {S N : Addr} {Z k : Nat} {nb : List Byte} (hs : Scr s S Z) (hZ : 256 ≤ Z)
    (h23 : s.gpr .r23 = S) (hN : word s.mem S oN = off N 0) (hNL : word s.mem S oNLen = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (off N i) = nb[i]'(by omega)) :
    WP isa checkN s fun t =>
      (t.gpr .r26 = BitVec.ofNat 64 0 -
          BitVec.ofNat 64 (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4, .r6, .r12, .r15, .r16, .r18, .r26] s t := by
  have hnw := hs.nowrap
  unfold checkN
  refine WP.seq (WP.mono (WP.keep [.r12, .r6] (Q := fun t => t.gpr .r12 = off N 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s.mem) ?_ (by decide)) fun s₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  · have hN' : s.mem.readW (off S 8) 64 = off N 0 := hN
    have hNL' : s.mem.readW (off S 16) 64 = BitVec.ofNat 64 k := hNL
    prun [h23, oN, oNLen, hs.ld (show 8 + 8 ≤ Z by omega), hs.ld (show 16 + 8 ≤ Z by omega), hN', hNL']
  refine WP.seq (WP.mono (check_ok (nb := nb) a12 a6 hk hk' hlen (by rw [k1.rd, k1.wr]; exact hrd)
    fun i hi => by rw [m1]; exact hb i hi) fun s₂ ⟨hv, m2, k2⟩ => ?_)
  refine WP.mono (WP.keep [.r3, .r4, .r26] (Q := fun t => t.gpr .r26 = BitVec.ofNat 64 0 -
    ((((s₂.gpr .r0 >>> 1) ||| (s₂.gpr .r0 &&& 1#64)) - 1#64) >>> 63) ∧ t.mem = s₂.mem) ?_ (by decide))
    fun t ⟨⟨t26, tm⟩, k3⟩ => ⟨⟨?_, tm.trans (m2.trans m1)⟩, ((k1.trans k2).trans k3).mono⟩
  · prun
  · rw [t26, isZero_bits]
    by_cases h0 : s₂.gpr .r0 = 0
    · simp only [h0, hv.mp h0, ↓reduceIte]
    · have h1 : ¬ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true := fun h => h0 (hv.mpr h)
      simp only [h0, h1, Bool.false_eq_true, ↓reduceIte]

/-- `cmpLt a m`, with array `a`'s digit `2 w` zero: `r20 :=` all ones if
array `a` is below array `m`, else 0, through array 3; `r10` back to array 0. -/
theorem cmpLt_ok {s : State} {B : Addr} {Z w a m : Nat} (hs : Scr s B Z) (ha : a < 8) (hm : m < 8)
    (ha3 : a ≠ 3) (hm3 : m ≠ 3) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0)) (h21 : s.gpr .r21 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (htop : word s.mem B (slot w a + 8 * w) = 0) :
    WP isa (cmpLt a m) s fun t =>
      (t.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64
          (if Mont.val32 s.mem B (slot w a) (2 * w) < Mont.val32 s.mem B (slot w m) (2 * w) then 1 else 0) ∧
        Mont.Outside B (slot w 3) (8 * w) s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
      Keep [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20] s t := by
  have hnw := hs.nowrap
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sm := Nat.le_trans (slot_le (w := w) hm) hZ
  have s3 := Nat.le_trans (slot_le (w := w) (j := 3) (by decide)) hZ
  have d3a := slot_sep (w := w) (Ne.symm ha3)
  have d3m := slot_sep (w := w) (Ne.symm hm3)
  unfold cmpLt
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) h10 h29 a) fun s₁ ⟨⟨a8, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) 3) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) m) fun s₃ ⟨⟨a10, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w a) (dT := slot w 3) (dM := slot w m)
    (hs.congr k13.wr) ((k3.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans a8))
    ((k3.gpr _ (by decide)).trans a9) a10
    ((k13.gpr _ (by decide)).trans h11) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun s₄ ⟨⟨c, hc, hD, h20⟩, out, k4⟩ => ?_)
  have k14 := k13.trans k4
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₄.mem)
    (by prun [(k14.gpr .r21 (by decide)).trans h21]) (by decide)) fun t ⟨⟨t10, tm⟩, k5⟩ =>
    ⟨⟨?_, by rw [m3, m2, m1] at out; rw [tm]; exact out.mono (Nat.le_refl _) (by omega), t10⟩,
      (k14.trans k5).mono⟩
  rw [k5.gpr .r20 (by decide), h20, m3, m2, m1]
  rw [m3, m2, m1] at hD
  have h0 : Mont.w32 s.mem B (slot w a + 4 * (2 * w)) = 0 := by
    have := Mont.word_eq_w32 s.mem B (slot w a + 8 * w)
    rw [show Mont.word s.mem B (slot w a + 8 * w) = 0 from htop, show (0 : BitVec 64).toNat = 0 from rfl,
      show slot w a + 8 * w = slot w a + 4 * (2 * w) by omega] at this
    omega
  rw [h0]
  have hDl' := Mont.val32_lt s₄.mem B (slot w 3) (2 * w)
  have hAl := Mont.val32_lt s.mem B (slot w a) (2 * w)
  have hMl := Mont.val32_lt s.mem B (slot w m) (2 * w)
  congr 2
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · simp only [Nat.lt_irrefl, ite_false]
    have h : ¬ Mont.val32 s.mem B (slot w a) (2 * w) < Mont.val32 s.mem B (slot w m) (2 * w) := by omega
    simp only [h, ite_false]
  · simp only [Nat.zero_lt_one, ite_true]
    have h : Mont.val32 s.mem B (slot w a) (2 * w) < Mont.val32 s.mem B (slot w m) (2 * w) := by omega
    simp only [h, ite_true]

/-- `checkLt a m`: `r26 &=` `cmpLt a m`'s mask. -/
theorem checkLt_ok {s : State} {B : Addr} {Z w a m : Nat} (hs : Scr s B Z) (ha : a < 8) (hm : m < 8)
    (ha3 : a ≠ 3) (hm3 : m ≠ 3) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0)) (h21 : s.gpr .r21 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (htop : word s.mem B (slot w a + 8 * w) = 0) :
    WP isa (checkLt a m) s fun t =>
      (t.gpr .r26 = s.gpr .r26 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64
          (if Mont.val32 s.mem B (slot w a) (2 * w) < Mont.val32 s.mem B (slot w m) (2 * w) then 1 else 0)) ∧
        Mont.Outside B (slot w 3) (8 * w) s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
      Keep [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20, .r26] s t := by
  unfold checkLt
  refine WP.seq (WP.mono (cmpLt_ok hs ha hm ha3 hm3 hw1 hw' hZ h10 h21 h29 h11 htop)
    fun s₁ ⟨⟨a20, o1, a10⟩, k1⟩ => ?_)
  refine WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 = s₁.gpr .r26 &&& s₁.gpr .r20 ∧ t.mem = s₁.mem)
    (by prun) (by decide)) fun t ⟨⟨t26, tm⟩, k2⟩ =>
    ⟨⟨by rw [t26, a20, k1.gpr .r26 (by decide)], by rw [tm]; exact o1, by rw [k2.gpr .r10 (by decide)]; exact a10⟩,
      (k1.trans k2).mono⟩

end VG.Proof.Bignum.PPC64LE.Crt
