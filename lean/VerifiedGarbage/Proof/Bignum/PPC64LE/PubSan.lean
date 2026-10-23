module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA public-key operation on PPC64LE: sanitizing `pre`

`sanitize_ok`: whatever `pre` held, `n` (array 0) is odd and at least 2 and
array 1 below it, as the Montgomery multiplications need; a valid modulus and
its `R² mod n` are unchanged.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

/-- `fixN`'s top word: `v`, or 1 if `v` is 0. -/
def fixTop (v : BitVec 64) : BitVec 64 :=
  v ||| (((v >>> 1) ||| (v &&& 1#64)) - 1#64) >>> 63

theorem fixTop_ne (v : BitVec 64) : fixTop v ≠ 0 ∧ (v ≠ 0 → fixTop v = v) := by
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
    have h0 : (((v >>> 1) ||| (v &&& 1#64)) - 1#64) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      show _ = 0
      omega
    have hv : v ≠ 0 := fun e => by subst e; simp at h
    simp only [fixTop, h0]
    exact ⟨by simpa using hv, fun _ => by simp⟩

theorem or_one_odd (v : BitVec 64) : (v ||| 1#64).toNat % 2 = 1 ∧ (v.toNat % 2 = 1 → v ||| 1#64 = v) := by
  have e : ∀ x : Nat, (x ||| 1) % 2 = 1 := fun x => by
    have := Nat.testBit_or x 1 0
    simp only [Nat.testBit_zero, Nat.one_mod, decide_true, Bool.or_true] at this
    exact of_decide_eq_true this
  refine ⟨by rw [BitVec.toNat_or]; exact e _, fun h => ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  rcases i with _ | i
  · simp [Nat.testBit_zero, h]
  · simp [Nat.testBit_succ]

theorem ofNat_shl2 (a : Nat) : BitVec.ofNat 64 a <<< 2 = BitVec.ofNat 64 (4 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `fixN`, then the bases of arrays 1 and 3 into `r8` and `r9`. -/
theorem fixN_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) :
    WP isa (.block (fixN ++ base .r8 1 ++ base .r9 3)) s fun t =>
      (t.mem = ((s.mem.writeW (off B (slot w 0)) (word s.mem B (slot w 0) ||| 1#64)).writeW
          (off B (slot w 0 + 8 * (w - 1))) (fixTop (word s.mem B (slot w 0 + 8 * (w - 1))))).writeW
          (off B (slot w 1 + 8 * w)) (0 : BitVec 64) ∧
        t.gpr .r8 = off B (slot w 1) ∧ t.gpr .r9 = off B (slot w 3)) ∧
      Keep [.r0, .r3, .r4, .r8, .r9, .r14] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r14] (Q := fun t => t.mem =
      ((s.mem.writeW (off B (slot w 0)) (word s.mem B (slot w 0) ||| 1#64)).writeW
          (off B (slot w 0 + 8 * (w - 1))) (fixTop (word s.mem B (slot w 0 + 8 * (w - 1))))).writeW
          (off B (slot w 1 + 8 * w)) (0 : BitVec 64) ∧ t.gpr .r10 = s.gpr .r10 ∧ t.gpr .r29 = s.gpr .r29) ?_ (by decide))
    fun t ⟨⟨tm, t10, t29⟩, kt⟩ => ?_
  · unfold fixN
    have a1 : BitVec.ofNat 64 (4 * (2 * w)) + off B (slot w 0) - BitVec.ofNat 64 8 =
        off B (slot w 0 + 8 * (w - 1)) := by
      rw [BitVec.add_comm, off_add, off, VG.Offset.add_ofNat_sub B (show 8 ≤ slot w 0 + 4 * (2 * w) by omega)]
      congr 2; omega
    have a2 : Mont.off B (slot w 0 + 8 * (w + 2) + 4 * (2 * w)) = off B (slot w 1 + 8 * w) := by
      simp only [Mont.off, off]; congr 2; omega
    have hr : ∀ v : BitVec 64, (s.mem.writeW (off B (slot w 0)) v).readW (off B (slot w 0 + 8 * (w - 1))) 64 =
        s.mem.readW (off B (slot w 0 + 8 * (w - 1))) 64 := fun v =>
      (writeW_outside s.mem B (d := slot w 0) v (by omega)).word (by omega) (by omega)
    prun [h10, h11, h29, ofNat_shl2, BitVec.add_zero, a1, a2, hs.ld (show slot w 0 + 8 ≤ Z by omega),
      hs.ld (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega), hr,
      hs.st (show slot w 0 + 8 ≤ Z by omega), hs.st (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega),
      hs.st (show slot w 1 + 8 * w + 8 ≤ Z by omega)]
    rfl
  · refine WP.mono (base_ok (rd := .r8) (by decide) (by decide) (t10.trans h10) (t29.trans h29) 1)
      fun t₁ ⟨⟨a8, m1⟩, k1⟩ => ?_
    refine WP.mono (base_ok (rd := .r9) (by decide) (by decide) ((k1.gpr _ (by decide)).trans (t10.trans h10))
      ((k1.gpr _ (by decide)).trans (t29.trans h29)) 3) fun t₂ ⟨⟨a9, m2⟩, k2⟩ =>
      ⟨⟨by rw [m2, m1, tm], (k2.gpr _ (by decide)).trans a8, a9⟩, ((kt.trans k1).trans k2).mono⟩

/-- `maskRR`: array 1's `w` words `&= r20`. -/
theorem maskRR_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 1 + 8 * w ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) :
    WP isa maskRR s fun t =>
      ((∀ i < w, word t.mem B (slot w 1 + 8 * i) = word s.mem B (slot w 1 + 8 * i) &&& s.gpr .r20) ∧
        Outside B (slot w 1) (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r17] s t := by
  have hnw := hs.nowrap
  unfold maskRR
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r14) (by decide) (by decide) h10 h29 1) fun s₀ ⟨⟨a14, m0⟩, k0⟩ => ?_
  have hpre : WP isa (.block [.lsr .d .r17 .r11 1]) s₀ fun s₁ =>
      (s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.mem = s₀.mem) ∧ Keep [.r17] s₀ s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [(k0.gpr .r11 (by decide)).trans h11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  refine WP.mono hpre fun s₁ ⟨⟨i17, im⟩, k₁⟩ => ?_
  have k01 := k0.trans k₁
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (slot w 1 + 8 * i) ∧ Outside B (slot w 1) (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (slot w 1 + 8 * k) = word s.mem B (slot w 1 + 8 * k) &&& s.gpr .r20) ∧
      Keep [.r0, .r14, .r17] s t
  refine WP.mono (wp_countdown (cnt := .r17) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j14, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr .r14 (by decide), a14]; rfl, by rw [im, m0]; exact Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega), k01.mono⟩ i17) fun t ⟨_, tout, tz, tk⟩ => ⟨⟨tz, tout⟩, tk⟩
  have h20 : t.gpr .r20 = s.gpr .r20 := jk.gpr _ (by decide)
  refine WP.mono (WP.keep [.r0, .r14, .r17] (Q := fun t' =>
    t'.mem = t.mem.writeW (off B (slot w 1 + 8 * i)) (word t.mem B (slot w 1 + 8 * i) &&& s.gpr .r20) ∧
      t'.gpr .r14 = off B (slot w 1 + 8 * (i + 1)) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) ?_ (by decide))
    fun t' ⟨⟨a, b, c⟩, k⟩ => ⟨⟨b, ?_, ?_, jk.trans' k⟩, c⟩
  · prun [j14, h20, (hs.congr jk.wr).ld (show slot w 1 + 8 * i + 8 ≤ Z by omega),
      (hs.congr jk.wr).st (show slot w 1 + 8 * i + 8 ≤ Z by omega)]
    simp only [Mont.off, off]; congr 2
  · have hw := writeW_outside t.mem B (d := slot w 1 + 8 * i) (word t.mem B (slot w 1 + 8 * i) &&& s.gpr .r20)
      (by omega)
    rw [a]; exact (jout.mono (Nat.le_refl _) (by omega)).trans (hw.mono (by omega) (by omega))
  · intro k hk
    have hw := writeW_outside t.mem B (d := slot w 1 + 8 * i) (word t.mem B (slot w 1 + 8 * i) &&& s.gpr .r20)
      (by omega)
    rw [a]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega) (by omega)]; exact jz k hk
    · rw [word_writeW_self, jout.word (Or.inr (Nat.le_refl _)) (by omega)]

theorem wv_top (m : Mem) (p : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m p d w = wv m p d (w - 1) + 2 ^ (64 * (w - 1)) * (word m p (d + 8 * (w - 1))).toNat := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel, wv]

theorem wv_low (m : Mem) (p : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m p d w % 2 = (word m p d).toNat % 2 := by
  obtain ⟨v, rfl⟩ : ∃ v, w = 1 + v := ⟨w - 1, by omega⟩
  simp only [wv_add, wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_one]
  omega

/-- `sanitize`: whatever arrays 0 and 1 held, array 0 is odd and at least 2,
its low word odd, and array 1 below it; if array 0 was odd with its top word
not zero, it is unchanged, and so is array 1 if it was below it. -/
theorem sanitize_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) :
    WP isa sanitize s fun t =>
      (Mont.val32 t.mem B (slot w 0) (2 * w) % 2 = 1 ∧ 2 ≤ Mont.val32 t.mem B (slot w 0) (2 * w) ∧
        (word t.mem B (slot w 0)).toNat % 2 = 1 ∧
        Mont.val32 t.mem B (slot w 1) (2 * w) < Mont.val32 t.mem B (slot w 0) (2 * w) ∧
        (Mont.val32 s.mem B (slot w 0) (2 * w) % 2 = 1 →
          2 ^ (64 * (w - 1)) ≤ Mont.val32 s.mem B (slot w 0) (2 * w) →
          Mont.val32 t.mem B (slot w 0) (2 * w) = Mont.val32 s.mem B (slot w 0) (2 * w) ∧
          (Mont.val32 s.mem B (slot w 1) (2 * w) < Mont.val32 s.mem B (slot w 0) (2 * w) →
            Mont.val32 t.mem B (slot w 1) (2 * w) = Mont.val32 s.mem B (slot w 1) (2 * w))) ∧
        Outside B (slot w 0) (4 * (8 * (w + 2))) s.mem t.mem) ∧
      Keep [.r0, .r3, .r4, .r8, .r9, .r14, .r15, .r16, .r17, .r20] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  simp only [Pre.val32_eq_wv]
  unfold sanitize
  refine WP.seq (WP.mono (fixN_ok hs hw2 hw' hZ h10 h29 h11) fun t₁ ⟨⟨tm, a8, a9⟩, k1⟩ => ?_)
  generalize hw0 : word s.mem B (slot w 0) = w0 at tm
  generalize htop : word s.mem B (slot w 0 + 8 * (w - 1)) = top at tm
  have o1 := writeW_outside s.mem B (d := slot w 0) (w0 ||| 1#64) (by omega)
  have o2 := writeW_outside (s.mem.writeW (off B (slot w 0)) (w0 ||| 1#64)) B (d := slot w 0 + 8 * (w - 1))
    (fixTop top) (by omega)
  have o3 := writeW_outside ((s.mem.writeW (off B (slot w 0)) (w0 ||| 1#64)).writeW
    (off B (slot w 0 + 8 * (w - 1))) (fixTop top)) B (d := slot w 1 + 8 * w) (0 : BitVec 64) (by omega)
  rw [← tm] at o3
  have W0 : word t₁.mem B (slot w 0) = w0 ||| 1#64 := by
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega), word_writeW_self]
  have WT : word t₁.mem B (slot w 0 + 8 * (w - 1)) = fixTop top := by
    rw [o3.word (by omega) (by omega), word_writeW_self]
  have WM : ∀ i, 0 < i → i < w - 1 → word t₁.mem B (slot w 0 + 8 * i) = word s.mem B (slot w 0 + 8 * i) :=
    fun i h0 h1 => by
      rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
  have W1 : ∀ i < w, word t₁.mem B (slot w 1 + 8 * i) = word s.mem B (slot w 1 + 8 * i) := fun i hi => by
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
  have Wz : word t₁.mem B (slot w 1 + 8 * w) = 0 := by rw [tm]; exact word_writeW_self _ _ _ _
  have Out1 : Outside B (slot w 0) (4 * (8 * (w + 2))) s.mem t₁.mem :=
    ((o1.mono (Nat.le_refl _) (by omega)).trans (o2.mono (by omega) (by omega))).trans (o3.mono (by omega) (by omega))
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w 1) (dT := slot w 3) (dM := slot w 0)
    (hs.congr k1.wr) a8 a9 ((k1.gpr _ (by decide)).trans h10) ((k1.gpr _ (by decide)).trans h11) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun t₂ ⟨⟨c, hc, hD, h20⟩, out2, k2⟩ => ?_)
  have k12 := k1.trans k2
  have out2' : Outside B (slot w 3) (8 * w) t₁.mem t₂.mem :=
    (show Outside B (slot w 3) (4 * (2 * w)) t₁.mem t₂.mem from fun x hx => out2 x hx).mono (Nat.le_refl _)
      (by omega)
  refine WP.mono (maskRR_ok (hs.congr k12.wr) (by omega) hw' (by omega) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) ((k12.gpr _ (by decide)).trans h11)) fun t ⟨⟨tw, out3⟩, k3⟩ =>
    ⟨?_, (k12.trans k3).mono⟩
  have hw0' : (w0 ||| 1#64).toNat % 2 = 1 := (or_one_odd w0).1
  have hft := fixTop_ne top
  have N3 : wv t.mem B (slot w 0) w = wv t₁.mem B (slot w 0) w := by
    rw [out3.wv (Or.inl (by omega)) (by omega), out2'.wv (Or.inl (by omega)) (by omega)]
  have Wt0 : word t.mem B (slot w 0) = w0 ||| 1#64 := by
    rw [out3.word (by omega) (by omega), out2'.word (by omega) (by omega), W0]
  have hN1 : wv t₁.mem B (slot w 0) w % 2 = 1 := by rw [wv_low _ _ _ (by omega), W0]; exact hw0'
  have h2 : 2 ≤ 2 ^ (64 * (w - 1)) :=
    Nat.le_trans (show 2 ≤ 2 ^ 1 by decide) (Nat.pow_le_pow_right (by decide) (by omega))
  have hN2 : 2 ^ (64 * (w - 1)) ≤ wv t₁.mem B (slot w 0) w := by
    rw [wv_top _ _ _ (by omega), WT]
    have h1 : 0 < (fixTop top).toNat := by
      rcases Nat.eq_zero_or_pos (fixTop top).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hft.1
      · exact h
    have := Nat.le_mul_of_pos_right (2 ^ (64 * (w - 1))) h1
    omega
  have R1 : wv t₁.mem B (slot w 1) w = wv s.mem B (slot w 1) w := wv_congr fun i hi => W1 i hi
  simp only [Pre.val32_eq_wv] at hD
  have h0 : Mont.w32 t₁.mem B (slot w 1 + 4 * (2 * w)) = 0 := by
    have := Mont.word_eq_w32 t₁.mem B (slot w 1 + 8 * w)
    rw [show Mont.word t₁.mem B (slot w 1 + 8 * w) = 0 from Wz, show (0 : BitVec 64).toNat = 0 from rfl,
      show slot w 1 + 8 * w = slot w 1 + 4 * (2 * w) by omega] at this
    omega
  rw [h0] at h20
  have hDl := wv_lt t₂.mem B (slot w 3) w
  rw [show 32 * (2 * w) = 64 * w by omega] at hD
  have hc1 : c = 1 ↔ wv t₁.mem B (slot w 1) w < wv t₁.mem B (slot w 0) w := by
    generalize 2 ^ (64 * w) = P at hD hDl
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
    · rw [Nat.mul_zero, Nat.add_zero] at hD; omega
    · rw [Nat.mul_one] at hD; omega
  have T1 : ∀ i < w, word t.mem B (slot w 1 + 8 * i) = word s.mem B (slot w 1 + 8 * i) &&& t₂.gpr .r20 :=
    fun i hi => by rw [tw i hi, out2'.word (Or.inl (by omega)) (by omega), W1 i hi]
  have R3 : wv t.mem B (slot w 1) w = if c = 1 then wv s.mem B (slot w 1) w else 0 := by
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
    · have hz : t₂.gpr .r20 = 0 := by rw [h20]; rfl
      exact (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by rw [T1 q hq, hz]; exact BitVec.and_zero
    · have hz : t₂.gpr .r20 = BitVec.allOnes 64 := by rw [h20]; rfl
      exact wv_congr fun i hi => by rw [T1 i hi, hz, BitVec.and_allOnes]
  refine ⟨by rw [N3]; exact hN1, by rw [N3]; omega, by rw [Wt0]; exact hw0', ?_, ?_, ?_⟩
  · rw [R3, N3]
    split
    · rename_i h; rw [← R1]; exact hc1.mp h
    · omega
  · intro hodd hbig
    have hw0o : w0.toNat % 2 = 1 := by rw [← hw0, ← wv_low _ _ _ (w := w) (by omega)]; exact hodd
    have e0 : w0 ||| 1#64 = w0 := (or_one_odd w0).2 hw0o
    have htop0 : top ≠ 0 := fun h => by
      have := wv_top s.mem B (slot w 0) (w := w) (by omega)
      rw [htop, h, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at this
      have := wv_lt s.mem B (slot w 0) (w - 1)
      omega
    have et : fixTop top = top := hft.2 htop0
    have NE : wv t₁.mem B (slot w 0) w = wv s.mem B (slot w 0) w := wv_congr fun i hi => by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [Nat.mul_zero, Nat.add_zero, W0, e0, hw0]
      · rcases (show i = w - 1 ∨ i < w - 1 by omega) with rfl | hi1
        · rw [WT, et, htop]
        · exact WM i hi0 hi1
    refine ⟨by rw [N3, NE], fun hlt => ?_⟩
    rw [R3, ite_eq_left_of_eq_true _ _ (eq_true (hc1.mpr (by rw [R1, NE]; exact hlt)))]
  · exact (Out1.trans (out2'.mono (by omega) (by omega))).trans (out3.mono (by omega) (by omega))

end VG.Proof.Bignum.PPC64LE.Pub
