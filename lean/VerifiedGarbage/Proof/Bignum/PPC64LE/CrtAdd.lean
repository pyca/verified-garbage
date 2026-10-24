module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: adding under a mask

`addMask_ok`: `T += M & mask` over `n` digits, modulo `2^(32 n)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- A digit of the addition, on bit vectors. -/
theorem add_arith (x y : BitVec 32) (c : BitVec 64) (b : Bool) (hc : c.toNat ≤ 1) :
    let D := x.setWidth 64 + (y.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))) + c
    (D >>> 32).toNat ≤ 1 ∧
      (D.setWidth 32).toNat + 2 ^ 32 * (D >>> 32).toNat = x.toNat + (if b then y.toNat else 0) + c.toNat := by
  intro D
  have hx := x.isLt
  have hy := y.isLt
  have hm : y.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) =
      if b then y.setWidth 64 else 0 := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact BitVec.and_zero
    · simp only [↓reduceIte]; exact BitVec.and_allOnes
  have vD : D.toNat = x.toNat + (if b then y.toNat else 0) + c.toNat := by
    simp only [D, hm]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_add, toNat_ext32] <;> simp <;> omega
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, vD]
  split <;> omega

/-- `addMask`, `T` (`n` digits) at `dT` (`r15`), `M` at `dM` (`r16`) apart from
it, and the mask of `b` in `r20`: `T := T + (b ? M : 0) mod 2^(32 n)`. -/
theorem addMask_ok {s : State} {B : Addr} {Z dT dM n : Nat} {b : Bool} (hs : Scr s B Z)
    (h15 : s.gpr .r15 = off B dT) (h16 : s.gpr .r16 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 n)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hT : dT + 4 * n ≤ Z) (hM : dM + 4 * n ≤ Z)
    (dTM : dT + 4 * n ≤ dM ∨ dM + 4 * n ≤ dT) :
    WP isa addMask s fun s' =>
      val32 s'.mem B dT n = (val32 s.mem B dT n + (if b then val32 s.mem B dM n else 0)) % 2 ^ (32 * n) ∧
      Outside B dT (4 * n) s.mem s'.mem ∧ Keep [.r0, .r3, .r15, .r16, .r17, .r24] s s' := by
  have hnw := hs.nowrap
  unfold addMask
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r17 .r11 0, .li .r24 0]) s
      fun s₁ => (s₁.gpr .r17 = BitVec.ofNat 64 n ∧ s₁.gpr .r24 = 0 ∧ s₁.mem = s.mem) ∧
        Keep [.r17, .r24] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h11, BitVec.add_zero]
    rfl
  refine WP.mono hpre fun s₁ ⟨⟨i17, i24, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r15 = off B (dT + 4 * i) ∧ t.gpr .r16 = off B (dM + 4 * i) ∧
      (t.gpr .r24).toNat ≤ 1 ∧ Outside B dT (4 * i) s.mem t.mem ∧
      val32 t.mem B dT i + 2 ^ (32 * i) * (t.gpr .r24).toNat =
        val32 s.mem B dT i + (if b then val32 s.mem B dM i else 0) ∧
      Keep [.r0, .r3, .r15, .r16, .r17, .r24] s t
  refine WP.mono (wp_countdown (body := .block ([.load .w .r0 .r15 0, .load .w .r3 .r16 0,
      .logic .and .r3 .r3 .r20, .add .r0 .r0 .r3, .add .r0 .r0 .r24, .store .w .r0 .r15 0, .lsr .d .r24 .r0 32,
      .addi .r15 .r15 4, .addi .r16 .r16 4] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := n) (by omega) (by omega) Inv (fun i hi t ⟨j15, j16, j24, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [k₁.gpr .r15 (by decide), h15]; rfl, by rw [k₁.gpr .r16 (by decide), h16]; rfl, by rw [i24]; decide,
      by rw [← im]; exact Outside.refl _ _ _ _, by cases b <;> simp [val32, i24], k₁.mono⟩ i17)
    fun t ⟨_, _, j24, jout, jeq, jk⟩ => ⟨?_, jout, jk⟩
  · have h20t : t.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) :=
      (jk.gpr _ (by decide)).trans h20
    have hst := (show WP isa (.block [.load .w .r0 .r15 0, .load .w .r3 .r16 0, .logic .and .r3 .r3 .r20,
        .add .r0 .r0 .r3, .add .r0 .r0 .r24, .store .w .r0 .r15 0, .lsr .d .r24 .r0 32, .addi .r15 .r15 4,
        .addi .r16 .r16 4, .subi .r17 .r17 1]) t fun t' =>
        let D := (t.mem.readW (off B (dT + 4 * i)) 32).setWidth 64 +
          ((t.mem.readW (off B (dM + 4 * i)) 32).setWidth 64 &&&
            (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))) + t.gpr .r24
        t'.gpr .r15 = off B (dT + 4 * i + 4) ∧ t'.gpr .r16 = off B (dM + 4 * i + 4) ∧
          t'.gpr .r24 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dT + 4 * i)) (D.setWidth 32) ∧
          Keep [.r0, .r3, .r15, .r16, .r17, .r24] t t' from by
      refine WP.mono (WP.keep [.r0, .r3, .r15, .r16, .r17, .r24] (Q := fun t' =>
        let D := (t.mem.readW (off B (dT + 4 * i)) 32).setWidth 64 +
          ((t.mem.readW (off B (dM + 4 * i)) 32).setWidth 64 &&&
            (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))) + t.gpr .r24
        t'.gpr .r15 = off B (dT + 4 * i + 4) ∧ t'.gpr .r16 = off B (dM + 4 * i + 4) ∧
          t'.gpr .r24 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dT + 4 * i)) (D.setWidth 32)) ?_ (by decide))
        fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
      prun [j15, j16, h20t, (hs.congr jk.wr).ld (show dT + 4 * i + 4 ≤ Z by omega),
        (hs.congr jk.wr).ld (show dM + 4 * i + 4 ≤ Z by omega),
        (hs.congr jk.wr).st (show dT + 4 * i + 4 ≤ Z by omega)])
    refine WP.mono hst fun t' ⟨l15, l16, l24, l17, lm, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l17⟩
    · rw [l15, show dT + 4 * i + 4 = dT + 4 * (i + 1) by omega]
    · rw [l16, show dM + 4 * i + 4 = dM + 4 * (i + 1) by omega]
    · rw [l24]; exact (add_arith _ _ _ b j24).1
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW32_outside _ B (d := dT + 4 * i) _ (by omega)).mono (by omega) (by omega))
    · have wx : w32 t.mem B (dT + 4 * i) = w32 s.mem B (dT + 4 * i) := jout.w32 (by omega) (by omega)
      have wy : w32 t.mem B (dM + 4 * i) = w32 s.mem B (dM + 4 * i) := jout.w32 (by omega) (by omega)
      have k := (add_arith (t.mem.readW (off B (dT + 4 * i)) 32) (t.mem.readW (off B (dM + 4 * i)) 32) _ b j24).2
      rw [lm, l24, val32_write_top _ _ _ _ _ (by omega), val32_succ s.mem B dT i, val32_succ s.mem B dM i,
        ← pow32_mul i]
      rw [← wx, ← wy]
      change _ + 2 ^ 32 * _ = w32 t.mem B (dT + 4 * i) + (if b then w32 t.mem B (dM + 4 * i) else 0) +
        (t.gpr .r24).toNat at k
      change _ = (_ + _ * w32 t.mem B (dT + 4 * i)) + (if b then (_ + _ * w32 t.mem B (dM + 4 * i)) else 0)
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at k jeq ⊢ <;> grind
  · have hl := val32_lt t.mem B dT n
    have hS : val32 s.mem B dT n + (if b then val32 s.mem B dM n else 0) =
        val32 t.mem B dT n + 2 ^ (32 * n) * (t.gpr .r24).toNat := jeq.symm
    rw [hS, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

end VG.Proof.Bignum.PPC64LE.Crt
