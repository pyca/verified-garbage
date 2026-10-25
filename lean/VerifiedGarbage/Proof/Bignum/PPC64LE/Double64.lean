module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModArith
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32

/-!
# Doubling modulo `n` on words of 64 bits, on PPC64LE

`double64_ok`: the accumulator's `w + 1` words := `2 x + b` for `x`'s `w`
words and the bit `b` in `r20`. `dblMod64_ok`: `x := 2 x + b mod n`, in the
arrays of `vg_rsa_mont_mul`, through `subMod64` and `selectAcc64`; and its
two uses, `doubleMod64_ok` and `doubleBitMod64_ok`, stated as
`doubleMod_ok` and `doubleBitMod_ok` (the same on digits of 32 bits).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute

/-- A word of the doubling: `2 x + c` is the low word of `(x << 1) + c` and
`2⁶⁴` times `x`'s top bit. -/
theorem dbl64_arith (x c : BitVec 64) (hc : c.toNat ≤ 1) :
    (x <<< 1 + c).toNat + 2 ^ 64 * (x >>> 63).toNat = 2 * x.toNat + c.toNat ∧ (x >>> 63).toNat ≤ 1 := by
  have hx := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega

/-- `double64`, `x` (`w` words) at `dX` (`r5`), the accumulator at `dA`
(`r8`) and the bit `b` in `r20`: the accumulator's `w + 1` words are `2 x +
b`. -/
theorem double64_ok {s : State} {B : Addr} {Z dA dX w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h5 : s.gpr .r5 = off B dX) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h20 : (s.gpr .r20).toNat ≤ 1) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 1) ≤ Z)
    (hX : dX + 8 * w ≤ Z) (dXA : dX + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dX) :
    WP isa double64 s fun s' =>
      wordsVal s'.mem B dA (w + 1) = 2 * wordsVal s.mem B dX w + (s.gpr .r20).toNat ∧
      Mont.Outside B dA (8 * (w + 1)) s.mem s'.mem ∧ Keep [.r0, .r3, .r14, .r15, .r17, .r20] s s' := by
  have hnw := hs.nowrap
  unfold double64
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .lsr .d .r17 .r11 1]) s
      fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dX ∧ s₁.gpr .r17 = BitVec.ofNat 64 w ∧
        s₁.mem = s.mem) ∧ Keep [.r14, .r15, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h5, h11, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega)]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i14, i15, i17, im⟩, k₁⟩ => ?_)
  have b₁ : s₁.gpr .r20 = s.gpr .r20 := k₁.gpr _ (by decide)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 8 * i) ∧ t.gpr .r15 = off B (dX + 8 * i) ∧ (t.gpr .r20).toNat ≤ 1 ∧
      Mont.Outside B dA (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dA i + 2 ^ (64 * i) * (t.gpr .r20).toNat = 2 * wordsVal s.mem B dX i + (s.gpr .r20).toNat ∧
      Keep [.r0, .r3, .r14, .r15, .r17, .r20] s₁ t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .r0 .r15 0, .lsl .r3 .r0 1, .add .r3 .r3 .r20,
      .lsr .d .r20 .r0 63, .store .d .r3 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j14, j15, j20, jout, jv, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [b₁]; exact h20, by rw [← im]; exact Mont.Outside.refl _ _ _ _,
      by simp [wordsVal, b₁], Keep.refl _ _⟩ i17)
    fun t ⟨t14, _, _, tout, tv, tk⟩ => ?_)
  · have hst : WP isa (.block [.load .d .r0 .r15 0, .lsl .r3 .r0 1, .add .r3 .r3 .r20, .lsr .d .r20 .r0 63,
        .store .d .r3 .r14 0, .addi .r14 .r14 8, .addi .r15 .r15 8, .subi .r17 .r17 1]) t
        fun t' => (t'.gpr .r14 = off B (dA + 8 * i + 8) ∧ t'.gpr .r15 = off B (dX + 8 * i + 8) ∧
          t'.gpr .r20 = word t.mem B (dX + 8 * i) >>> 63 ∧
          t'.mem = t.mem.writeW (off B (dA + 8 * i)) (word t.mem B (dX + 8 * i) <<< 1 + t.gpr .r20) ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1) ∧ Keep [.r0, .r3, .r14, .r15, .r17, .r20] t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [j14, j15, (hs.congr (k₁.trans jk).wr).ld (show dX + 8 * i + 8 ≤ Z by omega),
        (hs.congr (k₁.trans jk).wr).st (show dA + 8 * i + 8 ≤ Z by omega)]
    refine WP.mono hst fun t' ⟨⟨u14, u15, u20, um, u17⟩, uk⟩ => ⟨⟨u14.trans (by rw [Nat.mul_succ, Nat.add_assoc]),
      u15.trans (by rw [Nat.mul_succ, Nat.add_assoc]), ?_, ?_, ?_, (jk.trans uk).mono⟩, u17⟩
    · have := (dbl64_arith (word t.mem B (dX + 8 * i)) (t.gpr .r20) j20).2
      rw [u20]; exact this
    · rw [um]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dA + 8 * i) _ (by omega)).mono (by omega) (by omega))
    · have e := dbl64_arith (word t.mem B (dX + 8 * i)) (t.gpr .r20) j20
      have wx : word t.mem B (dX + 8 * i) = word s.mem B (dX + 8 * i) := jout.word (by omega) (by omega)
      rw [um, fios_wordsVal_write_top _ _ _ _ _ (by omega), u20, Nat.mul_succ, Nat.pow_add,
        wordsVal_succ_top s.mem B dX i]
      rw [wx] at e
      rw [wx]
      have := e.1
      grind
  · have hst : WP isa (.block [.store .d .r20 .r14 0]) t fun t' =>
        t' = { t with mem := t.mem.writeW (off B (dA + 8 * w)) (t.gpr .r20) } := by
      prun [t14, (hs.congr (k₁.trans tk).wr).st (show dA + 8 * w + 8 ≤ Z by omega)]
    refine WP.mono hst fun t' e => ?_
    subst e
    refine ⟨?_, ?_, ((k₁.trans tk).trans (Keep.mem _ _)).mono⟩
    · show wordsVal (t.mem.writeW (off B (dA + 8 * w)) (t.gpr .r20)) B dA (w + 1) = _
      rw [fios_wordsVal_write_top _ _ _ _ _ (by omega), ← tv]
    · exact (tout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dA + 8 * w) _ (by omega)).mono (by omega) (by omega))

/-- `dblMod64`, in the arrays of `vg_rsa_mont_mul` (`n` in array 0, `x` in
array 1, the accumulator and the temporary in arrays 2 and 3), `b` in `r20`:
`x := 2 x + b mod n`, changing only arrays 1–3. -/
theorem dblMod64_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h20 : (s.gpr .r20).toNat ≤ 1) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hx : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa dblMod64 s fun t =>
      val32 t.mem B (slot w 1) (2 * w) =
        (2 * val32 s.mem B (slot w 1) (2 * w) + (s.gpr .r20).toNat) % val32 s.mem B (slot w 0) (2 * w) ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  simp only [← wordsVal_eq_val32] at hx ⊢
  unfold dblMod64
  refine WP.seq (WP.mono (double64_ok (dA := slot w 2) (dX := slot w 1) hs h8 h5 h11 h20 hw hw' (by omega)
    (by omega) (by omega)) fun s₂ ⟨hd, out₂, k₂⟩ => ?_)
  have hs₂ := hs.congr k₂.wr
  have m₂ : wordsVal s₂.mem B (slot w 0) w = wordsVal s.mem B (slot w 0) w :=
    out₂.wordsVal (by omega) (by omega)
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₂
    (by rw [k₂.gpr .r8 (by decide), h8]) (by rw [k₂.gpr .r9 (by decide), h9])
    (by rw [k₂.gpr .r10 (by decide), h10]) (by rw [k₂.gpr .r11 (by decide), h11]) hw hw'
    (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₃ ⟨⟨c, hc, hD, h20'⟩, out₃, k₃⟩ => ?_)
  rw [m₂] at hD
  have hs₃ := hs₂.congr k₃.wr
  have k23 := k₂.trans k₃
  have accA : wordsVal s₃.mem B (slot w 2) w = wordsVal s₂.mem B (slot w 2) w :=
    out₃.wordsVal (by omega) (by omega)
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dO := slot w 1)
    (b := decide ((word s₂.mem B (slot w 2 + 8 * w)).toNat < c)) hs₃
    (by rw [k23.gpr .r8 (by decide), h8]) (by rw [k23.gpr .r9 (by decide), h9])
    (by rw [k23.gpr .r5 (by decide), h5]) (by rw [k23.gpr .r11 (by decide), h11])
    (by rw [h20']; simp only [decide_eq_true_eq]) hw hw' (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t ⟨hv, out₄, k₄⟩ => ⟨?_, ?_, (k23.trans k₄).mono⟩
  · rw [accA] at hv
    have hM := wordsVal_lt s.mem B (slot w 0) w
    rw [wordsVal_succ_top] at hd
    rw [hv, ← hd, ← Nat.add_zero (word s₂.mem B (slot w 2 + 8 * w)).toNat, ← Nat.mul_zero (2 ^ 64),
      ← VG.Proof.Bignum.csub_result hM (wordsVal_lt _ _ _ _) hc (wordsVal_lt _ _ _ _)
        (by rw [Nat.mul_zero, Nat.add_zero, hd]; omega) hD]
    by_cases h : (word s₂.mem B (slot w 2 + 8 * w)).toNat < c <;> simp [h]
  · exact ((out₂.mono (by omega) (by omega)).trans (out₃.mono (by omega) (by omega))).trans
      (out₄.mono (by omega) (by omega))

/-- `doubleMod64`: `doubleMod_ok` on words of 64 bits. -/
theorem doubleMod64_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hx : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa doubleMod64 s fun t =>
      val32 t.mem B (slot w 1) (2 * w) = 2 * val32 s.mem B (slot w 1) (2 * w) % val32 s.mem B (slot w 0) (2 * w) ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] s t := by
  unfold doubleMod64
  refine WP.seq (WP.mono (WP.keep [.r20] (Q := fun t => t.gpr .r20 = 0 ∧ t.mem = s.mem) (by prun; rfl) (by decide))
    fun s₁ ⟨⟨a20, m1⟩, k1⟩ => ?_)
  refine WP.mono (dblMod64_ok (hs.congr k1.wr) ((k1.gpr _ (by decide)).trans h8) ((k1.gpr _ (by decide)).trans h9)
    ((k1.gpr _ (by decide)).trans h10) ((k1.gpr _ (by decide)).trans h5) ((k1.gpr _ (by decide)).trans h11)
    (by rw [a20]; decide) hw hw' hZ (by rw [m1]; exact hx)) fun t ⟨tv, tout, tk⟩ => ⟨?_, ?_, (k1.trans tk).mono⟩
  · rw [tv, a20, m1]; rfl
  · rw [← m1]; exact tout

end VG.Proof.Bignum.PPC64LE

namespace VG.Proof.Bignum.PPC64LE.ModArith

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.ModArith VG.Proof.Bignum.PPC64LE

/-- `doubleBitMod64`: `doubleBitMod_ok` on words of 64 bits. -/
theorem doubleBitMod64_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hx : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa doubleBitMod64 s fun t =>
      val32 t.mem B (slot w 1) (2 * w) =
        (2 * val32 s.mem B (slot w 1) (2 * w) + (s.gpr .r24 >>> 63).toNat) % val32 s.mem B (slot w 0) (2 * w) ∧
      t.gpr .r24 = s.gpr .r24 <<< 1 ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧
      Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20, .r24] s t := by
  unfold doubleBitMod64
  refine WP.seq (WP.mono (WP.keep [.r20, .r24] (Q := fun t => t.gpr .r20 = s.gpr .r24 >>> 63 ∧
    t.gpr .r24 = s.gpr .r24 <<< 1 ∧ t.mem = s.mem) (by prun) (by decide)) fun s₁ ⟨⟨a20, a24, m1⟩, k1⟩ => ?_)
  have hb : (s₁.gpr .r20).toNat ≤ 1 := by
    rw [a20, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := (s.gpr .r24).isLt; omega
  refine WP.mono (dblMod64_ok (hs.congr k1.wr) ((k1.gpr _ (by decide)).trans h8) ((k1.gpr _ (by decide)).trans h9)
    ((k1.gpr _ (by decide)).trans h10) ((k1.gpr _ (by decide)).trans h5) ((k1.gpr _ (by decide)).trans h11)
    hb hw hw' hZ (by rw [m1]; exact hx)) fun t ⟨tv, tout, tk⟩ =>
    ⟨by rw [tv, a20, m1], by rw [tk.gpr .r24 (by decide), a24], by rw [← m1]; exact tout, (k1.trans tk).mono⟩

end VG.Proof.Bignum.PPC64LE.ModArith
