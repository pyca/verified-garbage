module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32

/-!
# The precomputed values of an RSA modulus on PPC64LE: doubling

`double_ok`: the accumulator's `n + 1` digits := twice the `n` digits of `x`.
`doubleMod_ok`: `x := 2 x mod n`, in the arrays of `vg_rsa_mont_mul`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute

/-- A digit of the doubling, on bit vectors: `D = 2 x + c`, whose low 32 bits
are the digit and whose bits above are the carry. -/
theorem dbl_arith (x : BitVec 32) (c : BitVec 64) (hc : c.toNat ≤ 1) :
    let D := x.setWidth 64 + x.setWidth 64 + c
    (D >>> 32).toNat ≤ 1 ∧ (D.setWidth 32).toNat + 2 ^ 32 * (D >>> 32).toNat = 2 * x.toNat + c.toNat := by
  intro D
  have hx := x.isLt
  have vD : D.toNat = 2 * x.toNat + c.toNat := by
    simp only [D, BitVec.toNat_add, toNat_ext32]
    omega
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, vD]
  omega

/-- `double`, `x` (`n` digits) at `dX` and the accumulator at `dA`: the
accumulator's `n + 1` digits are `2 x`. -/
theorem double_ok {s : State} {B : Addr} {Z dA dX n : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h5 : s.gpr .r5 = off B dX) (h11 : s.gpr .r11 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hA : dA + 4 * (n + 1) ≤ Z) (hX : dX + 4 * n ≤ Z)
    (dXA : dX + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dX) :
    WP isa double s fun s' =>
      val32 s'.mem B dA (n + 1) = 2 * val32 s.mem B dX n ∧
      Mont.Outside B dA (4 * (n + 1)) s.mem s'.mem ∧ Keep [.r0, .r14, .r15, .r17, .r20] s s' := by
  have hnw := hs.nowrap
  unfold double
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .addi .r17 .r11 0, .li .r20 0]) s
      fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dX ∧ s₁.gpr .r17 = BitVec.ofNat 64 n ∧
        s₁.gpr .r20 = 0 ∧ s₁.mem = s.mem) ∧ Keep [.r0, .r14, .r15, .r17, .r20] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h5, h11, BitVec.add_zero]
    rfl
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i17, i20, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 4 * i) ∧ t.gpr .r15 = off B (dX + 4 * i) ∧
      (t.gpr .r20).toNat ≤ 1 ∧ Mont.Outside B dA (4 * i) s.mem t.mem ∧
      val32 t.mem B dA i + 2 ^ (32 * i) * (t.gpr .r20).toNat = 2 * val32 s.mem B dX i ∧
      Keep [.r0, .r14, .r15, .r17, .r20] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .w .r0 .r15 0, .add .r0 .r0 .r0,
      .add .r0 .r0 .r20, .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4,
      .addi .r15 .r15 4] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := n) (by omega) (by omega) Inv (fun i hi t ⟨j14, j15, j20, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [i20]; decide,
      by rw [← im]; exact Mont.Outside.refl _ _ _ _, by simp [val32, i20], k₁⟩ i17)
    fun t ⟨j14, _, j20, jout, jeq, jk⟩ => ?_)
  · have hst := (show WP isa (.block [.load .w .r0 .r15 0, .add .r0 .r0 .r0, .add .r0 .r0 .r20,
        .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4, .addi .r15 .r15 4,
        .subi .r17 .r17 1]) t fun t' =>
        let D := (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 +
          (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 + t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dX + 4 * i + 4) ∧
          t'.gpr .r20 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 4 * i)) (D.setWidth 32) ∧
          Keep [.r0, .r14, .r15, .r17, .r20] t t' from by
      refine WP.mono (WP.keep [.r0, .r14, .r15, .r17, .r20] (Q := fun t' =>
        let D := (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 +
          (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 + t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dX + 4 * i + 4) ∧
          t'.gpr .r20 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 4 * i)) (D.setWidth 32)) ?_ (by decide))
        fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
      prun [j14, j15, (hs.congr jk.wr).ld (show dX + 4 * i + 4 ≤ Z by omega),
        (hs.congr jk.wr).st (show dA + 4 * i + 4 ≤ Z by omega)])
    refine WP.mono hst fun t' ⟨l14, l15, l20, l17, lm, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l17⟩
    · rw [l14, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega]
    · rw [l15, show dX + 4 * i + 4 = dX + 4 * (i + 1) by omega]
    · rw [l20]; exact (dbl_arith _ _ j20).1
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW32_outside _ B (d := dA + 4 * i) _ (by omega)).mono (by omega) (by omega))
    · have wx : w32 t.mem B (dX + 4 * i) = w32 s.mem B (dX + 4 * i) := jout.w32 (by omega) (by omega)
      have k := (dbl_arith (t.mem.readW (off B (dX + 4 * i)) 32) _ j20).2
      rw [lm, l20, val32_write_top _ _ _ _ _ (by omega), val32_succ s.mem B dX i, ← pow32_mul i]
      rw [← wx]
      change _ + 2 ^ 32 * _ = 2 * w32 t.mem B (dX + 4 * i) + (t.gpr .r20).toNat at k
      change _ = 2 * (_ + _ * w32 t.mem B (dX + 4 * i))
      grind
  · have hfin : WP isa (.block [.store .w .r20 .r14 0]) t fun t' =>
        t'.mem = t.mem.writeW (off B (dA + 4 * n)) ((t.gpr .r20).setWidth 32) ∧ Keep [] t t' := by
      refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B (dA + 4 * n))
        ((t.gpr .r20).setWidth 32)) ?_ (by decide)) fun t' ⟨h, k⟩ => ⟨h, k⟩
      prun [j14, (hs.congr jk.wr).st (show dA + 4 * n + 4 ≤ Z by omega)]
    refine WP.mono hfin fun t' ⟨lm, lk⟩ => ⟨?_, ?_, jk.trans' lk.mono⟩
    · rw [lm, val32_write_top _ _ _ _ _ (by omega), ← jeq]
      congr 2
      rw [BitVec.toNat_setWidth]
      omega
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW32_outside _ B (d := dA + 4 * n) _ (by omega)).mono (by omega) (by omega))

/-- `doubleMod`, with `n` in array 0, `x` in array 1, the accumulator in array
2 and the temporary in array 3: `x := 2 x mod n`, changing only arrays 1–3. -/
theorem doubleMod_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hx : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa doubleMod s fun t =>
      val32 t.mem B (slot w 1) (2 * w) = 2 * val32 s.mem B (slot w 1) (2 * w) % val32 s.mem B (slot w 0) (2 * w) ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  unfold doubleMod
  refine WP.seq (WP.mono (double_ok (n := 2 * w) (dA := slot w 2) (dX := slot w 1) hs h8 h5 h11 (by omega)
    (by omega) (by omega) (by omega) (by omega)) fun s₂ ⟨hd, out₂, k₂⟩ => ?_)
  have hs₂ := hs.congr k₂.wr
  have m₂ : val32 s₂.mem B (slot w 0) (2 * w) = val32 s.mem B (slot w 0) (2 * w) :=
    out₂.val32 (by omega) (by omega)
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₂
    (by rw [k₂.gpr .r8 (by decide), h8]) (by rw [k₂.gpr .r9 (by decide), h9])
    (by rw [k₂.gpr .r10 (by decide), h10]) (by rw [k₂.gpr .r11 (by decide), h11])
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₃ ⟨⟨c, hc, hD, h20⟩, out₃, k₃⟩ => ?_)
  rw [m₂] at hD
  have hs₃ := hs₂.congr k₃.wr
  have k23 := k₂.trans k₃
  have accA : val32 s₃.mem B (slot w 2) (2 * w) = val32 s₂.mem B (slot w 2) (2 * w) :=
    out₃.val32 (by omega) (by omega)
  refine WP.mono (selectAcc_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dO := slot w 1)
    (b := decide (w32 s₂.mem B (slot w 2 + 4 * (2 * w)) < c)) hs₃
    (by rw [k23.gpr .r8 (by decide), h8]) (by rw [k23.gpr .r9 (by decide), h9])
    (by rw [k23.gpr .r5 (by decide), h5]) (by rw [k23.gpr .r11 (by decide), h11])
    (by rw [h20]; simp only [decide_eq_true_eq])
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t ⟨hv, out₄, k₄⟩ => ⟨?_, ?_, (k23.trans k₄).mono⟩
  · rw [accA] at hv
    have hM := val32_lt s.mem B (slot w 0) (2 * w)
    rw [val32_succ] at hd
    rw [hv, ← hd, ← Nat.add_zero (w32 s₂.mem B (slot w 2 + 4 * (2 * w))),
      ← Nat.mul_zero (2 ^ 64),
      ← VG.Proof.Bignum.csub_result hM (val32_lt _ _ _ _) hc (val32_lt _ _ _ _) (by rw [Nat.mul_zero, Nat.add_zero]; omega) hD]
    by_cases h : w32 s₂.mem B (slot w 2 + 4 * (2 * w)) < c <;> simp [h]
  · exact ((out₂.mono (by omega) (by omega)).trans (out₃.mono (by omega) (by omega))).trans
      (out₄.mono (by omega) (by omega))

end VG.Proof.Bignum.PPC64LE
