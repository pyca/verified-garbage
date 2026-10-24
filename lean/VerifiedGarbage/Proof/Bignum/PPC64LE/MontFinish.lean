module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery multiplication on PPC64LE: zeroing, and the final subtraction

`zeroAcc_ok`: the accumulator's first `w + 1` words := 0. `subMod_ok`: `T -
m` into the temporary, with the borrow out of the top digit as a mask.
`selectAcc_ok`: the result, `T` or `T - m` by the mask.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE

/-! ## Zeroing the accumulator -/

theorem val32_zero {m : Mem} {B : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m B (d + 4 * j) = 0) → val32 m B d k = 0
  | 0, _ => rfl
  | k + 1, h => by rw [val32_succ, val32_zero fun j hj => h j (by omega_arith), h k (by omega_arith), Nat.mul_zero]

theorem toNat_ofNat_shr1 {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n >>> 1).toNat = n / 2 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]

/-- `zeroAcc`, the accumulator at `dA` and `n = 2 w` in `r11`: its first `w +
1` words, the `n + 2` digits, are 0. -/
theorem zeroAcc_ok {s : State} {B : Addr} {Z dA w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : w < 2 ^ 31)
    (hA : dA + 8 * (w + 1) ≤ Z) :
    WP isa zeroAcc s fun s' =>
      (∀ j < 2 * w + 2, w32 s'.mem B (dA + 4 * j) = 0) ∧ Outside B dA (8 * (w + 1)) s.mem s'.mem ∧
        Keep [.r0, .r14, .r17] s s' := by
  have hnw := hs.nowrap
  unfold zeroAcc
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .lsr .d .r17 .r11 1, .addi .r17 .r17 1, .li .r0 0]) s
      fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r17 = BitVec.ofNat 64 (w + 1) ∧ s₁.gpr .r0 = 0 ∧
        s₁.mem = s.mem) ∧ Keep [.r0, .r14, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h11]
    refine ⟨?_, rfl⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, toNat_ofNat_shr1 (by omega_arith), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  refine WP.mono hpre fun s₁ ⟨⟨i14, i17, i0, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 8 * i) ∧ t.gpr .r0 = 0 ∧ Outside B dA (8 * i) s.mem t.mem ∧
      (∀ k < i, word t.mem B (dA + 8 * k) = 0) ∧ Keep [.r0, .r14, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .r0 .r14 0, .addi .r14 .r14 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w + 1) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, i0, by rw [← im]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₁⟩ i17) fun t ⟨_, _, tout, tz, tk⟩ => ⟨fun j hj => ?_, tout, tk⟩
  · have hst : WP isa (.block [.store .d .r0 .r14 0, .addi .r14 .r14 8, .subi .r17 .r17 1]) t
        fun t' => t' = ((({ t with mem := t.mem.writeW (off B (dA + 8 * i)) (0 : BitVec 64) } : State).write
          .r14 (off B (dA + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1)) := by
      prun [j14, j0, (hs.congr jk.wr).st (show dA + 8 * i + 8 ≤ Z by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw := writeW_outside t.mem B (d := dA + 8 * i) 0 (by omega_arith)
    refine ⟨⟨by gsimp; rw [show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith], by gsimp; exact j0, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))
    · intro k hk
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
      · exact word_writeW_self _ _ _ _
    · exact jk.trans' ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono)
  · have hword := word_eq_w32 t.mem B (dA + 8 * (j / 2))
    rw [tz (j / 2) (by omega_arith)] at hword
    have : w32 t.mem B (dA + 8 * (j / 2)) = 0 ∧ w32 t.mem B (dA + 8 * (j / 2) + 4) = 0 := by
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at hword; omega_arith
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · rw [show dA + 4 * j = dA + 8 * (j / 2) by omega_arith]; exact this.1
    · rw [show dA + 4 * j = dA + 8 * (j / 2) + 4 by omega_arith]; exact this.2

/-! ## The subtraction of `m` -/

/-- A digit of a subtraction, on bit vectors: `d = t - m - c` in 64 bits,
whose sign bit is the borrow and whose low 32 bits are the digit. -/
theorem sub_arith (t m : BitVec 32) (c : BitVec 64) (hc : c.toNat ≤ 1) :
    let D := t.setWidth 64 - m.setWidth 64 - c
    (D >>> 63).toNat ≤ 1 ∧
      c.toNat + (D.setWidth 32).toNat + m.toNat = t.toNat + 2 ^ 32 * (D >>> 63).toNat := by
  intro D
  have ht := t.isLt
  have hm := m.isLt
  have vD : D.toNat = (2 ^ 64 - c.toNat + ((2 ^ 64 - m.toNat) + t.toNat) % 2 ^ 64) % 2 ^ 64 := by
    simp only [D, BitVec.toNat_sub, toNat_ext32]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, vD]
  omega_arith

/-- The sign bit of `t - c` is whether `t < c`. -/
theorem sel_arith (t : BitVec 32) (c : BitVec 64) (hc : c.toNat ≤ 1) :
    ((t.setWidth 64 - c) >>> 63).toNat = if t.toNat < c.toNat then 1 else 0 := by
  have ht := t.isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, toNat_ext32]
  split <;> omega_arith

/-- `subMod`, the accumulator `T` (`n + 1` digits) at `dA`, the temporary at
`dT` and `m` at `dM`: the temporary's first `n` digits are `D` with `D + m =
T_L + 2^(32 n) c` (`T_L` the low `n` digits of `T`, `c` the borrow), and
`r20` the mask of `tₙ < c`, all ones or 0. -/
theorem subMod_ok {s : State} {B : Addr} {Z dA dT dM n : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h9 : s.gpr .r9 = off B dT) (h10 : s.gpr .r10 = off B dM)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hA : dA + 4 * (n + 1) ≤ Z) (hT : dT + 4 * n ≤ Z) (hM : dM + 4 * n ≤ Z)
    (dTA : dT + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dT) (dTM : dT + 4 * n ≤ dM ∨ dM + 4 * n ≤ dT) :
    WP isa subMod s fun s' =>
      (∃ c ≤ 1, val32 s'.mem B dT n + val32 s.mem B dM n = val32 s.mem B dA n + 2 ^ (32 * n) * c ∧
        s'.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if w32 s.mem B (dA + 4 * n) < c then 1 else 0)) ∧
      Outside B dT (4 * n) s.mem s'.mem ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] s s' := by
  have hnw := hs.nowrap
  unfold subMod
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r16 .r10 0, .addi .r17 .r11 0,
      .li .r20 0]) s fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dT ∧ s₁.gpr .r16 = off B dM ∧
        s₁.gpr .r17 = BitVec.ofNat 64 n ∧ s₁.gpr .r20 = 0 ∧ s₁.mem = s.mem) ∧
        Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h9, h10, h11, BitVec.add_zero]
    rfl
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i16, i17, i20, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 4 * i) ∧ t.gpr .r15 = off B (dT + 4 * i) ∧ t.gpr .r16 = off B (dM + 4 * i) ∧
      (t.gpr .r20).toNat ≤ 1 ∧ Outside B dT (4 * i) s.mem t.mem ∧
      val32 t.mem B dT i + val32 s.mem B dM i = val32 s.mem B dA i + 2 ^ (32 * i) * (t.gpr .r20).toNat ∧
      Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .w .r0 .r14 0, .load .w .r3 .r16 0,
      .sub .r0 .r0 .r3, .sub .r0 .r0 .r20, .store .w .r0 .r15 0, .lsr .d .r20 .r0 63, .addi .r14 .r14 4,
      .addi .r15 .r15 4, .addi .r16 .r16 4] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := n) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j15, j16, j20, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [i16]; rfl, by rw [i20]; decide,
      by rw [← im]; exact Outside.refl _ _ _ _, by simp [val32, i20], k₁⟩ i17)
    fun t ⟨j14, _, _, j20, jout, jeq, jk⟩ => ?_)
  · have hst := (show WP isa (.block [.load .w .r0 .r14 0, .load .w .r3 .r16 0, .sub .r0 .r0 .r3,
        .sub .r0 .r0 .r20, .store .w .r0 .r15 0, .lsr .d .r20 .r0 63, .addi .r14 .r14 4, .addi .r15 .r15 4,
        .addi .r16 .r16 4, .subi .r17 .r17 1]) t fun t' =>
        let D := (t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 -
          (t.mem.readW (off B (dM + 4 * i)) 32).setWidth 64 - t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dT + 4 * i + 4) ∧
          t'.gpr .r16 = off B (dM + 4 * i + 4) ∧ t'.gpr .r20 = D >>> 63 ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dT + 4 * i)) (D.setWidth 32) ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] t t' from by
      refine WP.mono (WP.keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] (Q := fun t' =>
        let D := (t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 -
          (t.mem.readW (off B (dM + 4 * i)) 32).setWidth 64 - t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dT + 4 * i + 4) ∧
          t'.gpr .r16 = off B (dM + 4 * i + 4) ∧ t'.gpr .r20 = D >>> 63 ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dT + 4 * i)) (D.setWidth 32)) ?_ (by decide))
        fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k⟩
      prun [j14, j15, j16, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
        (hs.congr jk.wr).ld (show dM + 4 * i + 4 ≤ Z by omega_arith),
        (hs.congr jk.wr).st (show dT + 4 * i + 4 ≤ Z by omega_arith)])
    refine WP.mono hst fun t' ⟨l14, l15, l16, l20, l17, lm, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l17⟩
    · rw [l14, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
    · rw [l15, show dT + 4 * i + 4 = dT + 4 * (i + 1) by omega_arith]
    · rw [l16, show dM + 4 * i + 4 = dM + 4 * (i + 1) by omega_arith]
    · rw [l20]; exact (sub_arith _ _ _ j20).1
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW32_outside _ B (d := dT + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) := jout.w32 (by omega_arith) (by omega_arith)
      have wm : w32 t.mem B (dM + 4 * i) = w32 s.mem B (dM + 4 * i) := jout.w32 (by omega_arith) (by omega_arith)
      have k := (sub_arith (t.mem.readW (off B (dA + 4 * i)) 32) (t.mem.readW (off B (dM + 4 * i)) 32) _ j20).2
      rw [lm, l20, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dM i, val32_succ s.mem B dA i,
        ← pow32_mul i]
      change _ + _ + (_ + _ * w32 s.mem B (dM + 4 * i)) = _ + _ * w32 s.mem B (dA + 4 * i) + _
      rw [← wa, ← wm]
      change (t.gpr .r20).toNat + _ + w32 t.mem B (dM + 4 * i) = w32 t.mem B (dA + 4 * i) + _ at k
      grind
  · have hfin : WP isa (.block [.load .w .r0 .r14 0, .sub .r0 .r0 .r20, .lsr .d .r0 .r0 63, .li .r3 0,
        .sub .r20 .r3 .r0]) t fun t' =>
        (t'.gpr .r20 = BitVec.ofNat 64 0 - ((t.mem.readW (off B (dA + 4 * n)) 32).setWidth 64 - t.gpr .r20) >>> 63 ∧
          t'.mem = t.mem) ∧ Keep [.r0, .r3, .r20] t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [j14, (hs.congr jk.wr).ld (show dA + 4 * n + 4 ≤ Z by omega_arith)]
    refine WP.mono hfin fun t' ⟨⟨l20, lm⟩, lk⟩ => ⟨⟨(t.gpr .r20).toNat, j20, by rw [lm]; exact jeq, ?_⟩,
      by rw [lm]; exact jout, jk.trans' (lk.mono (by decide))⟩
    have wa : w32 t.mem B (dA + 4 * n) = w32 s.mem B (dA + 4 * n) := jout.w32 (by omega_arith) (by omega_arith)
    rw [l20, ← wa]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [sel_arith _ _ j20]
    split <;> rfl

/-! ## The selection -/

/-- A digit of the selection, on bit vectors. -/
theorem select_arith (x y : BitVec 32) (b : Bool) :
    (((y.setWidth 64 ^^^ x.setWidth 64) &&&
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))) ^^^ x.setWidth 64).setWidth 32 =
      if b then y else x := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, BitVec.sub_zero, BitVec.and_zero,
      BitVec.zero_xor]
    exact lo32_ext x
  · simp only [ite_true, show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl,
      BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact lo32_ext y

/-- `selectAcc`, the mask of `b` in `r20`: the `n` digits at `o` (`dO`) are
those of the accumulator (`dA`) if `b`, else the temporary's (`dT`). -/
theorem selectAcc_ok {s : State} {B : Addr} {Z dA dT dO n : Nat} (hs : Scr s B Z) {b : Bool}
    (h8 : s.gpr .r8 = off B dA) (h9 : s.gpr .r9 = off B dT) (h5 : s.gpr .r5 = off B dO)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 n)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) (hn : 1 ≤ n)
    (hn' : n < 2 ^ 32) (hA : dA + 4 * n ≤ Z) (hT : dT + 4 * n ≤ Z) (hO : dO + 4 * n ≤ Z)
    (dOA : dO + 4 * n ≤ dA ∨ dA + 4 * n ≤ dO) (dOT : dO + 4 * n ≤ dT ∨ dT + 4 * n ≤ dO) :
    WP isa selectAcc s fun s' =>
      val32 s'.mem B dO n = (if b then val32 s.mem B dA n else val32 s.mem B dT n) ∧
      Outside B dO (4 * n) s.mem s'.mem ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17] s s' := by
  have hnw := hs.nowrap
  unfold selectAcc
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r16 .r5 0, .addi .r17 .r11 0]) s
      fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dT ∧ s₁.gpr .r16 = off B dO ∧
        s₁.gpr .r17 = BitVec.ofNat 64 n ∧ s₁.mem = s.mem) ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h9, h5, h11, BitVec.add_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i16, i17, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 4 * i) ∧ t.gpr .r15 = off B (dT + 4 * i) ∧ t.gpr .r16 = off B (dO + 4 * i) ∧
      Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i = (if b then val32 s.mem B dA i else val32 s.mem B dT i) ∧
      Keep [.r0, .r3, .r14, .r15, .r16, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .w .r0 .r15 0, .load .w .r3 .r14 0,
      .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r20, .logic .xor .r3 .r3 .r0, .store .w .r3 .r16 0,
      .addi .r14 .r14 4, .addi .r15 .r15 4, .addi .r16 .r16 4] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := n) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j15, j16, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [i16]; rfl, by rw [← im]; exact Outside.refl _ _ _ _,
      by simp only [val32]; split <;> rfl, k₁⟩ i17)
    fun t ⟨_, _, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have r20 : t.gpr .r20 = s.gpr .r20 := jk.gpr _ (by decide)
  have hst : WP isa (.block [.load .w .r0 .r15 0, .load .w .r3 .r14 0, .logic .xor .r3 .r3 .r0,
      .logic .and .r3 .r3 .r20, .logic .xor .r3 .r3 .r0, .store .w .r3 .r16 0, .addi .r14 .r14 4,
      .addi .r15 .r15 4, .addi .r16 .r16 4, .subi .r17 .r17 1]) t fun t' =>
      (t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dT + 4 * i + 4) ∧
        t'.gpr .r16 = off B (dO + 4 * i + 4) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i))
          (if b then t.mem.readW (off B (dA + 4 * i)) 32 else t.mem.readW (off B (dT + 4 * i)) 32)) ∧
      Keep [.r0, .r3, .r14, .r15, .r16, .r17] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j14, j15, j16, r20, h20, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dT + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith), select_arith]
  refine WP.mono hst fun t' ⟨⟨l14, l15, l16, l17, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l17⟩
  · rw [l14, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l15, show dT + 4 * i + 4 = dT + 4 * (i + 1) by omega_arith]
  · rw [l16, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) := jout.w32 (by omega_arith) (by omega_arith)
    have wt : w32 t.mem B (dT + 4 * i) = w32 s.mem B (dT + 4 * i) := jout.w32 (by omega_arith) (by omega_arith)
    rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), jeq, val32_succ s.mem B dA i, val32_succ s.mem B dT i]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [← wt]
    · simp only [ite_true]; rw [← wa]

end VG.Proof.Bignum.PPC64LE
