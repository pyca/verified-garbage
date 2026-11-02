module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Bignum.PackedRead
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA public-key operation on RISC-V: sanitizing `pre`

`sanitize_ok`: whatever `pre` held, `n` (array 0) is made odd and at least 2
and `R² mod n` (array 1) below it, without changing the values of a valid
modulus (`fixN`, then `subMod64`'s mask applied by `maskRR`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot wv wv_congr wv_lt wv_add wv_eq_zero_iff)
open VG.Proof.Mont (wordsVal)

theorem san_wordsVal_eq_wv (m : Mem) (P : Addr) (d W : Nat) : wordsVal m P d W = wv m P d W := by
  rw [VG.Proof.Bignum.wordsVal_read, VG.Proof.Bignum.read_eq_wv]

theorem outside_wv {B : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.Mont.Outside B o n m m') {d k : Nat}
    (hd : d + 8 * k ≤ o ∨ o + n ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) : wv m' B d k = wv m B d k := by
  rw [← san_wordsVal_eq_wv, ← san_wordsVal_eq_wv]; exact VG.Proof.Mont.Outside.wordsVal h hd hd'

/-- `fixN`'s top word: `v`, or 1 if `v` is 0. -/
def fixTop (v : BitVec 64) : BitVec 64 :=
  v ||| (((v >>> 1) ||| (v &&& 1#64)) - 1#64) >>> 63

theorem fixTop_ne (v : BitVec 64) : fixTop v ≠ 0 ∧ (v ≠ 0 → fixTop v = v) := by
  by_cases h : v.toNat ≤ 1
  · rcases (show v = 0 ∨ v = 1 by
      rcases (show v.toNat = 0 ∨ v.toNat = 1 by omega_arith) with h | h
      · exact Or.inl (BitVec.eq_of_toNat_eq h)
      · exact Or.inr (BitVec.eq_of_toNat_eq h)) with rfl | rfl <;> decide
  · have hu1 : 1 ≤ ((v >>> 1) ||| (v &&& 1#64)).toNat := by
      have := Nat.left_le_or (n := (v >>> 1).toNat) (m := (v &&& 1#64).toNat)
      rw [BitVec.toNat_or]
      have : (v >>> 1).toNat = v.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega_arith
    have hu2 : ((v >>> 1) ||| (v &&& 1#64)).toNat < 2 ^ 63 := by
      rw [BitVec.toNat_or]
      apply Nat.or_lt_two_pow
      · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := v.isLt; omega_arith
      · rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have h0 : (((v >>> 1) ||| (v &&& 1#64)) - 1#64) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      show _ = 0
      omega_arith
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

/-- `fixN`, then the bases of arrays 1 and 3 into `a5` and `a6`. -/
theorem fixN_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) :
    WP isa (.block (fixN ++ base .a5 1 ++ base .a6 3)) s fun t =>
      (t.mem = ((s.mem.writeW (off B (slot w 0)) (Mont.word s.mem B (slot w 0) ||| 1#64)).writeW
          (off B (slot w 0 + 8 * (w - 1))) (fixTop (Mont.word s.mem B (slot w 0 + 8 * (w - 1))))).writeW
          (off B (slot w 1 + 8 * w)) (0 : BitVec 64) ∧
        t.gpr .a5 = off B (slot w 1) ∧ t.gpr .a6 = off B (slot w 3)) ∧
      Keep [.a5, .a6, .s0, .s1, .s2, .t3] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have al := slot_al w
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.s0, .s1, .s2, .t3] (Q := fun t => t.mem =
      ((s.mem.writeW (off B (slot w 0)) (Mont.word s.mem B (slot w 0) ||| 1#64)).writeW
          (off B (slot w 0 + 8 * (w - 1))) (fixTop (Mont.word s.mem B (slot w 0 + 8 * (w - 1))))).writeW
          (off B (slot w 1 + 8 * w)) (0 : BitVec 64) ∧ t.gpr .a7 = s.gpr .a7 ∧ t.gpr .s5 = s.gpr .s5) ?_
      (by rfl) (by rfl))
    fun t ⟨⟨tm, t7, t5⟩, kt⟩ => ?_
  · unfold fixN
    have a1 : BitVec.ofNat 64 (8 * w) + off B (slot w 0) - BitVec.ofNat 64 8 =
        off B (slot w 0 + 8 * (w - 1)) := by
      rw [BitVec.add_comm, off_add, off_sub B (show 8 ≤ slot w 0 + 8 * w by omega_arith)]
      congr 2; omega_arith
    have a2 : off B (slot w 0 + 8 * (w + 2) + 8 * w) = off B (slot w 1 + 8 * w) := by
      congr 2; omega_arith
    have hr : ∀ v : BitVec 64, (s.mem.writeW (off B (slot w 0)) v).readW (off B (slot w 0 + 8 * (w - 1))) 64 =
        s.mem.readW (off B (slot w 0 + 8 * (w - 1))) 64 := fun v =>
      (VG.Proof.Mont.writeW_outside s.mem B (d := slot w 0) v (by omega_arith)).word (by omega_arith) (by omega_arith)
    brun [h7, h0, h5, Pre.ofNat_shl3, add_ofNat_zero, a1, a2, exec_li, hs.ld (show slot w 0 + 8 ≤ Z by omega_arith),
      hs.ld (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega_arith), hr,
      hs.st (show slot w 0 + 8 ≤ Z by omega_arith), hs.st (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega_arith),
      hs.st (show slot w 1 + 8 * w + 8 ≤ Z by omega_arith),
      hs.al8 (show slot w 0 + 8 ≤ Z by omega_arith) (al 0),
      hs.al8 (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega_arith) (by have := al 0; omega_arith),
      hs.al8 (show slot w 1 + 8 * w + 8 ≤ Z by omega_arith) (by have := al 1; omega_arith)]
    rfl
  · refine WP.mono (base_ok (rd := .a5) (by decide) (t7.trans h7) (t5.trans h5) 1)
      fun t₁ ⟨⟨a5', m1⟩, k1⟩ => ?_
    refine WP.mono (base_ok (rd := .a6) (by decide) ((k1.gpr (by decide)).trans (t7.trans h7))
      ((k1.gpr (by decide)).trans (t5.trans h5)) 3) fun t₂ ⟨⟨a6', m2⟩, k2⟩ =>
      ⟨⟨by rw [m2, m1, tm], (k2.gpr (by decide)).trans a5', a6'⟩, ((kt.trans k1).trans k2).mono (by decide)⟩

/-- `maskRR`: array 1's `w` words `&= s4`. -/
theorem maskRR_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 1 + 8 * w ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) :
    WP isa maskRR s fun t =>
      ((∀ i < w, Mont.word t.mem B (slot w 1 + 8 * i) = Mont.word s.mem B (slot w 1 + 8 * i) &&& s.gpr .s4) ∧
        VG.Proof.Mont.Outside B (slot w 1) (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t5] s t := by
  have hnw := hs.nowrap
  have al1 := slot_al w 1
  unfold maskRR
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .t3) (by decide) h7 h5 1) fun s₀ ⟨⟨a3, m0⟩, k0⟩ => ?_
  have hpre : WP isa (.block [.addi .t5 .t0 0]) s₀ fun s₁ =>
      (s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.mem = s₀.mem) ∧ Keep [.t5] s₀ s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(k0.gpr (r := .t0) (by decide)).trans h0, add_ofNat_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i5, im⟩, k₁⟩ => ?_
  have k01 := k0.trans k₁
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w 1 + 8 * i) ∧ VG.Proof.Mont.Outside B (slot w 1) (8 * i) s.mem t.mem ∧
      (∀ k < i, Mont.word t.mem B (slot w 1 + 8 * k) = Mont.word s.mem B (slot w 1 + 8 * k) &&& s.gpr .s4) ∧
      Keep [.s0, .t3, .t5] s t
  refine WP.mono (wp_countdown (cnt := .t5) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j3, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr (by decide), a3]; rfl, by rw [im, m0]; exact VG.Proof.Mont.Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega_arith), k01.mono (by decide)⟩ i5) fun t ⟨_, tout, tz, tk⟩ => ⟨⟨tz, tout⟩, tk⟩
  have h4 : t.gpr .s4 = s.gpr .s4 := jk.gpr (by decide)
  refine WP.mono (WP.keep [.s0, .t3, .t5] (Q := fun t' =>
    t'.mem = t.mem.writeW (off B (slot w 1 + 8 * i)) (Mont.word t.mem B (slot w 1 + 8 * i) &&& s.gpr .s4) ∧
      t'.gpr .t3 = off B (slot w 1 + 8 * (i + 1)) ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ?_
      (by rfl) (by rfl))
    fun t' ⟨⟨a, b, c⟩, k⟩ => ⟨⟨b, ?_, ?_, Keep.trans' jk k⟩, c⟩
  · brun [j3, h4, add_ofNat_zero, (hs.congr jk.2.2).ld (show slot w 1 + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).st (show slot w 1 + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show slot w 1 + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    rfl
  · have hw := VG.Proof.Mont.writeW_outside t.mem B (d := slot w 1 + 8 * i) (Mont.word t.mem B (slot w 1 + 8 * i) &&& s.gpr .s4)
      (by omega_arith)
    rw [a]; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
  · intro k hk
    have hw := VG.Proof.Mont.writeW_outside t.mem B (d := slot w 1 + 8 * i) (Mont.word t.mem B (slot w 1 + 8 * i) &&& s.gpr .s4)
      (by omega_arith)
    rw [a]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
    · rw [VG.Proof.Mont.word_writeW_self, jout.word (Or.inr (Nat.le_refl _)) (by omega_arith)]

theorem wv_top (m : Mem) (p : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m p d w = wv m p d (w - 1) + 2 ^ (64 * (w - 1)) * (Mont.word m p (d + 8 * (w - 1))).toNat := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega_arith⟩
  simp only [Nat.add_sub_cancel, wv]

theorem wv_low (m : Mem) (p : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m p d w % 2 = (Mont.word m p d).toNat % 2 := by
  obtain ⟨v, rfl⟩ : ∃ v, w = 1 + v := ⟨w - 1, by omega_arith⟩
  simp only [wv_add, wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_one]
  omega_arith

/-- `sanitize`: whatever arrays 0 and 1 held, array 0 is odd and at least 2,
its low word odd, and array 1 below it; if array 0 was odd with its top word
not zero, it is unchanged, and so is array 1 if it was below it. -/
theorem sanitize_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) :
    WP isa sanitize s fun t =>
      (wordsVal t.mem B (slot w 0) w % 2 = 1 ∧ 2 ≤ wordsVal t.mem B (slot w 0) w ∧
        (Mont.word t.mem B (slot w 0)).toNat % 2 = 1 ∧
        wordsVal t.mem B (slot w 1) w < wordsVal t.mem B (slot w 0) w ∧
        (wordsVal s.mem B (slot w 0) w % 2 = 1 →
          2 ^ (64 * (w - 1)) ≤ wordsVal s.mem B (slot w 0) w →
          wordsVal t.mem B (slot w 0) w = wordsVal s.mem B (slot w 0) w ∧
          (wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w →
            wordsVal t.mem B (slot w 1) w = wordsVal s.mem B (slot w 1) w)) ∧
        VG.Proof.Mont.Outside B (slot w 0) (4 * (8 * (w + 2))) s.mem t.mem) ∧
      Keep [.a0, .a5, .a6, .s0, .s1, .s2, .s3, .s4, .t3, .t4, .t5] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  simp only [san_wordsVal_eq_wv]
  unfold sanitize
  refine WP.seq (WP.mono (fixN_ok hs hw2 hw' hZ h7 h5 h0) fun t₁ ⟨⟨tm, a5', a6'⟩, k1⟩ => ?_)
  generalize hw0 : Mont.word s.mem B (slot w 0) = w0 at tm
  generalize htop : Mont.word s.mem B (slot w 0 + 8 * (w - 1)) = top at tm
  have o1 := VG.Proof.Mont.writeW_outside s.mem B (d := slot w 0) (w0 ||| 1#64) (by omega_arith)
  have o2 := VG.Proof.Mont.writeW_outside (s.mem.writeW (off B (slot w 0)) (w0 ||| 1#64)) B (d := slot w 0 + 8 * (w - 1))
    (fixTop top) (by omega_arith)
  have o3 := VG.Proof.Mont.writeW_outside ((s.mem.writeW (off B (slot w 0)) (w0 ||| 1#64)).writeW
    (off B (slot w 0 + 8 * (w - 1))) (fixTop top)) B (d := slot w 1 + 8 * w) (0 : BitVec 64) (by omega_arith)
  rw [← tm] at o3
  have W0 : Mont.word t₁.mem B (slot w 0) = w0 ||| 1#64 := by
    rw [o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith), VG.Proof.Mont.word_writeW_self]
  have WT : Mont.word t₁.mem B (slot w 0 + 8 * (w - 1)) = fixTop top := by
    rw [o3.word (by omega_arith) (by omega_arith), VG.Proof.Mont.word_writeW_self]
  have WM : ∀ i, 0 < i → i < w - 1 → Mont.word t₁.mem B (slot w 0 + 8 * i) = Mont.word s.mem B (slot w 0 + 8 * i) :=
    fun i h0 h1 => by
      rw [o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]
  have W1 : ∀ i < w, Mont.word t₁.mem B (slot w 1 + 8 * i) = Mont.word s.mem B (slot w 1 + 8 * i) := fun i hi => by
    rw [o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]
  have Wz : Mont.word t₁.mem B (slot w 1 + 8 * w) = 0 := by rw [tm]; exact VG.Proof.Mont.word_writeW_self _ _ _ _
  have Out1 : VG.Proof.Mont.Outside B (slot w 0) (4 * (8 * (w + 2))) s.mem t₁.mem :=
    ((o1.mono (Nat.le_refl _) (by omega_arith)).trans (o2.mono (by omega_arith) (by omega_arith))).trans (o3.mono (by omega_arith) (by omega_arith))
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 1) (dT := slot w 3) (dM := slot w 0)
    (hs.congr k1.2.2) a5' a6' ((k1.gpr (by decide)).trans h7) ((k1.gpr (by decide)).trans h0) (by omega_arith) hw'
    (slot_al w 1) (slot_al w 3) (slot_al w 0) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t₂ ⟨⟨c, hc, hD, h4⟩, out2', k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (maskRR_ok (hs.congr k12.2.2) (by omega_arith) hw' (by omega_arith) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h5) ((k12.gpr (by decide)).trans h0)) fun t ⟨⟨tw, out3⟩, k3⟩ =>
    ⟨?_, (k12.trans k3).mono (by decide)⟩
  have hw0' : (w0 ||| 1#64).toNat % 2 = 1 := (or_one_odd w0).1
  have hft := fixTop_ne top
  have N3 : wv t.mem B (slot w 0) w = wv t₁.mem B (slot w 0) w := by
    rw [outside_wv out3 (Or.inl (by omega_arith)) (by omega_arith), outside_wv out2' (Or.inl (by omega_arith)) (by omega_arith)]
  have Wt0 : Mont.word t.mem B (slot w 0) = w0 ||| 1#64 := by
    rw [out3.word (by omega_arith) (by omega_arith), out2'.word (by omega_arith) (by omega_arith), W0]
  have hN1 : wv t₁.mem B (slot w 0) w % 2 = 1 := by rw [wv_low _ _ _ (by omega_arith), W0]; exact hw0'
  have h2 : 2 ≤ 2 ^ (64 * (w - 1)) :=
    Nat.le_trans (show 2 ≤ 2 ^ 1 by decide) (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have hN2 : 2 ^ (64 * (w - 1)) ≤ wv t₁.mem B (slot w 0) w := by
    rw [wv_top _ _ _ (by omega_arith), WT]
    have h1 : 0 < (fixTop top).toNat := by
      rcases Nat.eq_zero_or_pos (fixTop top).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hft.1
      · exact h
    have := Nat.le_mul_of_pos_right (2 ^ (64 * (w - 1))) h1
    omega_arith
  have R1 : wv t₁.mem B (slot w 1) w = wv s.mem B (slot w 1) w := wv_congr fun i hi => W1 i hi
  simp only [san_wordsVal_eq_wv] at hD
  rw [Wz] at h4
  have hDl := wv_lt t₂.mem B (slot w 3) w
  have hc1 : c = 1 ↔ wv t₁.mem B (slot w 1) w < wv t₁.mem B (slot w 0) w := by
    generalize 2 ^ (64 * w) = P at hD hDl
    rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl
    · rw [Nat.mul_zero, Nat.add_zero] at hD; omega_arith
    · rw [Nat.mul_one] at hD; omega_arith
  have T1 : ∀ i < w, Mont.word t.mem B (slot w 1 + 8 * i) = Mont.word s.mem B (slot w 1 + 8 * i) &&& t₂.gpr .s4 :=
    fun i hi => by rw [tw i hi, out2'.word (Or.inl (by omega_arith)) (by omega_arith), W1 i hi]
  have R3 : wv t.mem B (slot w 1) w = if c = 1 then wv s.mem B (slot w 1) w else 0 := by
    rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl
    · have hz : t₂.gpr .s4 = 0 := by rw [h4]; rfl
      exact (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by rw [T1 q hq, hz]; exact BitVec.and_zero
    · have hz : t₂.gpr .s4 = BitVec.allOnes 64 := by rw [h4]; rfl
      exact wv_congr fun i hi => by rw [T1 i hi, hz, BitVec.and_allOnes]
  refine ⟨by rw [N3]; exact hN1, by rw [N3]; omega_arith, by rw [Wt0]; exact hw0', ?_, ?_, ?_⟩
  · rw [R3, N3]
    split
    · rename_i h; rw [← R1]; exact hc1.mp h
    · omega_arith
  · intro hodd hbig
    have hw0o : w0.toNat % 2 = 1 := by rw [← hw0, ← wv_low _ _ _ (w := w) (by omega_arith)]; exact hodd
    have e0 : w0 ||| 1#64 = w0 := (or_one_odd w0).2 hw0o
    have htop0 : top ≠ 0 := fun h => by
      have := wv_top s.mem B (slot w 0) (w := w) (by omega_arith)
      rw [htop, h, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at this
      have := wv_lt s.mem B (slot w 0) (w - 1)
      omega_arith
    have et : fixTop top = top := hft.2 htop0
    have NE : wv t₁.mem B (slot w 0) w = wv s.mem B (slot w 0) w := wv_congr fun i hi => by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [Nat.mul_zero, Nat.add_zero, W0, e0, hw0]
      · rcases (show i = w - 1 ∨ i < w - 1 by omega_arith) with rfl | hi1
        · rw [WT, et, htop]
        · exact WM i hi0 hi1
    refine ⟨by rw [N3, NE], fun hlt => ?_⟩
    rw [R3, ite_eq_left_of_eq_true _ _ (eq_true (hc1.mpr (by rw [R1, NE]; exact hlt)))]
  · exact (Out1.trans (out2'.mono (by omega_arith) (by omega_arith))).trans (out3.mono (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.RISCV64.Pub
