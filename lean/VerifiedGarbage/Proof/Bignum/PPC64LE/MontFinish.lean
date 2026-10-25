module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery multiplication on PPC64LE: zeroing, and the final subtraction

`mont_newton64`: `-m⁻¹ mod 2⁶⁴` by a step of Newton's iteration. `subMod_ok`: `T -
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

/-- A step of Newton's iteration: `m y ≡ -1 (mod 2³²)` gives `m y (2 + m y) ≡
-1 (mod 2⁶⁴)`, since `m y (2 + m y) + 1 = (m y + 1)²`. -/
theorem mont_newton64 (m y : BitVec 64) (h : (m.toNat % 2 ^ 32 * y.toNat + 1) % 2 ^ 32 = 0) :
    (m.toNat * ((m * y + BitVec.ofNat 64 2) * y).toNat + 1) % 2 ^ 64 = 0 := by
  have e : m * ((m * y + BitVec.ofNat 64 2) * y) + 1#64 = (m * y + 1#64) * (m * y + 1#64) := by
    grind
  have hq : (m * y + 1#64).toNat % 2 ^ 32 = 0 := by
    have hm : m.toNat % 2 ^ 32 * y.toNat % 2 ^ 32 = m.toNat * y.toNat % 2 ^ 32 := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [BitVec.toNat_add, BitVec.toNat_mul, show (1#64).toNat = 1 from rfl]
    omega
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_mul m, BitVec.toNat_mul (m * y + 1#64)] at e'
  obtain ⟨q, hq'⟩ : ∃ q, (m * y + 1#64).toNat = 2 ^ 32 * q := ⟨_, (Nat.div_add_mod _ _).symm.trans (by rw [hq, Nat.add_zero])⟩
  rw [hq', show 2 ^ 32 * q * (2 ^ 32 * q) = 2 ^ 64 * (q * q) by grind, Nat.mul_mod_right,
    show (1#64).toNat = 1 from rfl, Nat.mod_add_mod] at e'
  exact e'

theorem mont_ofNat_shr1 {n : Nat} (hn : n < 2 ^ 63) : BitVec.ofNat 64 (2 * n) >>> 1 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

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
