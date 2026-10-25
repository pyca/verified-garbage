module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Montgomery multiplication on PPC64LE: zeroing, and the final subtraction in words

`zeroAcc_ok`: the accumulator's first `w + 1` words := 0, and the rounds'
count. `subMod64_ok`: `T - m` into the temporary, word by word with the
borrow in CA, and the borrow out of the top word as a mask.
`selectAcc64_ok`: the result, `T` or `T - m` by the mask.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum.PPC64LE

/-! ## Zeroing the accumulator -/

/-- `zeroAcc`, with `n = 2 w` in `r11` and the accumulator at `dA`: its
first `w + 1` words 0 and `w` in `r4`. -/
theorem zeroAcc_ok {s : State} {B : Addr} {Z dA w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : w < 2 ^ 31) (hA : dA + 8 * (w + 1) ≤ Z) :
    WP isa zeroAcc s fun s' =>
      wordsVal s'.mem B dA (w + 1) = 0 ∧ Outside B dA (8 * (w + 1)) s.mem s'.mem ∧
        s'.gpr .r4 = BitVec.ofNat 64 w ∧ Keep [.r4, .r14, .r17, .r22] s s' := by
  have hnw := hs.nowrap
  unfold zeroAcc
  refine WP.seq ?_
  have hpre : WP isa (.block [.lsr .d .r4 .r11 1, .addi .r14 .r8 0, .addi .r17 .r4 1, .li .r22 0]) s
      fun s₁ => (s₁.gpr .r4 = BitVec.ofNat 64 w ∧ s₁.gpr .r14 = off B dA ∧
        s₁.gpr .r17 = BitVec.ofNat 64 (w + 1) ∧ s₁.gpr .r22 = 0 ∧ s₁.mem = s.mem) ∧
        Keep [.r4, .r14, .r17, .r22] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h11, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega_arith)]
    exact ⟨(BitVec.ofNat_add _ _).symm, rfl⟩
  refine WP.mono hpre fun s₁ ⟨⟨i4, i14, i17, i22, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 8 * i) ∧ t.gpr .r22 = 0 ∧ Outside B dA (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dA i = 0 ∧ Keep [.r14, .r17] s₁ t
  refine WP.mono (wp_countdown (body := .block ([.store .d .r22 .r14 0, .addi .r14 .r14 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := w + 1) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j14, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, i22, by rw [← im]; exact Outside.refl _ _ _ _, rfl, Keep.refl _ _⟩ i17)
    fun t ⟨_, _, tout, tz, tk⟩ => ⟨tz, tout, by rw [tk.gpr _ (by decide)]; exact i4, (k₁.trans tk).mono⟩
  have hst : WP isa (.block [.store .d .r22 .r14 0, .addi .r14 .r14 8, .subi .r17 .r17 1]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (off B (dA + 8 * i)) (0 : BitVec 64) } : State).write
        .r14 (off B (dA + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1)) := by
    prun [j14, j0, (hs.congr (k₁.trans jk).wr).st (show dA + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  refine ⟨⟨by gsimp; rw [show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside t.mem B (d := dA + 8 * i) 0 (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · gsimp
    rw [fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), jz]
    rfl
  · exact jk.trans' ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono)

/-! ## The subtraction of `m` -/

/-- A word of a subtraction: `n - m - b` (`b` the borrow, CA clear) is its
low word and its borrow out. -/
theorem sub64_arith (n m : BitVec 64) (ca : Bool) :
    (BitVec.ofNat 64 (n.toNat + (2 ^ 64 - 1 - m.toNat) + ca.toNat)).toNat + m.toNat + (!ca).toNat =
      n.toNat + 2 ^ 64 * (!decide (2 ^ 64 ≤ n.toNat + (2 ^ 64 - 1 - m.toNat) + ca.toNat)).toNat := by
  have hn := n.isLt
  have hm := m.isLt
  have hc := Bool.toNat_le ca
  have hnc : (!ca).toNat = 1 - ca.toNat := by cases ca <;> rfl
  rw [BitVec.toNat_ofNat, hnc]
  by_cases h : 2 ^ 64 ≤ n.toNat + (2 ^ 64 - 1 - m.toNat) + ca.toNat <;>
    simp only [h, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.toNat_true,
      Bool.toNat_false] <;> omega_arith

/-- `subMod64`, the accumulator `T` (`w + 1` words) at `dA`, the temporary at
`dT` and `m` at `dM`: the temporary's first `w` words are `D` with `D + m =
T_L + 2^(64 w) c` (`T_L` the low `w` words of `T`, `c` the borrow), and
`r20` the mask of `t_w < c`, all ones or 0. -/
theorem subMod64_ok {s : State} {B : Addr} {Z dA dT dM w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h9 : s.gpr .r9 = off B dT) (h10 : s.gpr .r10 = off B dM)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hA : dA + 8 * (w + 1) ≤ Z) (hT : dT + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dTA : dT + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dT) (dTM : dT + 8 * w ≤ dM ∨ dM + 8 * w ≤ dT) :
    WP isa subMod64 s fun s' =>
      (∃ c ≤ 1, wordsVal s'.mem B dT w + wordsVal s.mem B dM w = wordsVal s.mem B dA w + 2 ^ (64 * w) * c ∧
        s'.gpr .r20 = if (word s.mem B (dA + 8 * w)).toNat < c then BitVec.allOnes 64 else 0) ∧
      Outside B dT (8 * w) s.mem s'.mem ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] s s' := by
  have hnw := hs.nowrap
  unfold subMod64
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r16 .r10 0, .lsr .d .r17 .r11 1,
      .subc .r0 .r0 .r0]) s fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dT ∧
        s₁.gpr .r16 = off B dM ∧ s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.ca = true ∧ s₁.mem = s.mem) ∧
        Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    mcrun [h8, h9, h10, h11, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega_arith)]
    have := (s.gpr .r0).isLt
    simp only [decide_eq_true_eq]
    omega_arith
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i16, i17, ica, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 8 * i) ∧ t.gpr .r15 = off B (dT + 8 * i) ∧ t.gpr .r16 = off B (dM + 8 * i) ∧
      Outside B dT (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dT i + wordsVal s.mem B dM i = wordsVal s.mem B dA i + 2 ^ (64 * i) * (!t.ca).toNat ∧
      Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .r0 .r14 0, .load .d .r3 .r16 0,
      .sube .r0 .r0 .r3, .store .d .r0 .r15 0, .addi .r14 .r14 8, .addi .r15 .r15 8, .addi .r16 .r16 8] ++
      ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j15, j16, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [i16]; rfl, by rw [← im]; exact Outside.refl _ _ _ _,
      by simp [wordsVal, ica], k₁⟩ i17)
    fun t ⟨j14, _, _, jout, jeq, jk⟩ => ?_)
  · have hst : WP isa (.block [.load .d .r0 .r14 0, .load .d .r3 .r16 0, .sube .r0 .r0 .r3, .store .d .r0 .r15 0,
        .addi .r14 .r14 8, .addi .r15 .r15 8, .addi .r16 .r16 8, .subi .r17 .r17 1]) t fun t' =>
        (t'.gpr .r14 = off B (dA + 8 * i + 8) ∧ t'.gpr .r15 = off B (dT + 8 * i + 8) ∧
          t'.gpr .r16 = off B (dM + 8 * i + 8) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dT + 8 * i)) (BitVec.ofNat 64 ((word t.mem B (dA + 8 * i)).toNat +
            (2 ^ 64 - 1 - (word t.mem B (dM + 8 * i)).toNat) + t.ca.toNat)) ∧
          t'.ca = decide (2 ^ 64 ≤ (word t.mem B (dA + 8 * i)).toNat +
            (2 ^ 64 - 1 - (word t.mem B (dM + 8 * i)).toNat) + t.ca.toNat)) ∧
        Keep [.r0, .r3, .r14, .r15, .r16, .r17, .r20] t t' := by
      refine WP.keep _ ?_ (by decide)
      mcrun [j14, j15, j16, (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
        (hs.congr jk.wr).ld (show dM + 8 * i + 8 ≤ Z by omega_arith),
        (hs.congr jk.wr).st (show dT + 8 * i + 8 ≤ Z by omega_arith)]
    refine WP.mono hst fun t' ⟨⟨l14, l15, l16, l17, lm, lca⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l17⟩
    · rw [l14, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
    · rw [l15, show dT + 8 * i + 8 = dT + 8 * (i + 1) by omega_arith]
    · rw [l16, show dM + 8 * i + 8 = dM + 8 * (i + 1) by omega_arith]
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW_outside _ B (d := dT + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) := jout.word (by omega_arith) (by omega_arith)
      have wm : word t.mem B (dM + 8 * i) = word s.mem B (dM + 8 * i) := jout.word (by omega_arith) (by omega_arith)
      have k := sub64_arith (word t.mem B (dA + 8 * i)) (word t.mem B (dM + 8 * i)) t.ca
      rw [← lca, wa, wm] at k
      rw [lm, fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dM i,
        wordsVal_succ_top s.mem B dA i, Nat.mul_succ, Nat.pow_add, wa, wm]
      have e : 2 ^ (64 * i) * (BitVec.ofNat 64 ((word s.mem B (dA + 8 * i)).toNat +
          (2 ^ 64 - 1 - (word s.mem B (dM + 8 * i)).toNat) + t.ca.toNat)).toNat +
          2 ^ (64 * i) * (word s.mem B (dM + 8 * i)).toNat + 2 ^ (64 * i) * (!t.ca).toNat =
          2 ^ (64 * i) * (word s.mem B (dA + 8 * i)).toNat + 2 ^ (64 * i) * 2 ^ 64 * (!t'.ca).toNat := by
        rw [← Nat.mul_add, ← Nat.mul_add, Nat.mul_assoc, ← Nat.mul_add, k]
      grind
  · have hfin : WP isa (.block [.load .d .r0 .r14 0, .li .r3 0, .sube .r0 .r0 .r3, .sube .r20 .r20 .r20]) t
        fun t' => (t'.gpr .r20 = BitVec.ofNat 64 ((t.gpr .r20).toNat + (2 ^ 64 - 1 - (t.gpr .r20).toNat) +
          (decide (2 ^ 64 ≤ (word t.mem B (dA + 8 * w)).toNat + (2 ^ 64 - 1 - 0) + t.ca.toNat)).toNat) ∧
          t'.mem = t.mem) ∧ Keep [.r0, .r3, .r20] t t' := by
      refine WP.keep _ ?_ (by decide)
      mcrun [j14, (hs.congr jk.wr).ld (show dA + 8 * w + 8 ≤ Z by omega_arith)]
      rfl
    refine WP.mono hfin fun t' ⟨⟨l20, lm⟩, lk⟩ => ⟨⟨(!t.ca).toNat, Bool.toNat_le _, by rw [lm]; exact jeq, ?_⟩,
      by rw [lm]; exact jout, jk.trans' (lk.mono (by decide))⟩
    have wa : word t.mem B (dA + 8 * w) = word s.mem B (dA + 8 * w) := jout.word (by omega_arith) (by omega_arith)
    rw [l20, ← wa]
    have := (t.gpr .r20).isLt
    rw [show (t.gpr .r20).toNat + (2 ^ 64 - 1 - (t.gpr .r20).toNat) = 2 ^ 64 - 1 by omega_arith]
    cases t.ca <;> by_cases h : (word t.mem B (dA + 8 * w)).toNat = 0 <;> simp [h]
    rw [decide_eq_true (by omega_arith : 1 ≤ (word t.mem B (dA + 8 * w)).toNat)]
    rfl

/-! ## The selection -/

/-- A word of the selection. -/
theorem select64_arith (x y : BitVec 64) (b : Bool) :
    ((y ^^^ x) &&& (if b then BitVec.allOnes 64 else 0)) ^^^ x = if b then y else x := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, BitVec.zero_xor]
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- `selectAcc64`, the mask of `b` in `r20`: the `w` words at `o` (`dO`) are
those of the accumulator (`dA`) if `b`, else the temporary's (`dT`). -/
theorem selectAcc64_ok {s : State} {B : Addr} {Z dA dT dO w : Nat} (hs : Scr s B Z) {b : Bool}
    (h8 : s.gpr .r8 = off B dA) (h9 : s.gpr .r9 = off B dT) (h5 : s.gpr .r5 = off B dO)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h20 : s.gpr .r20 = if b then BitVec.allOnes 64 else 0) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hA : dA + 8 * w ≤ Z) (hT : dT + 8 * w ≤ Z) (hO : dO + 8 * w ≤ Z)
    (dOA : dO + 8 * w ≤ dA ∨ dA + 8 * w ≤ dO) (dOT : dO + 8 * w ≤ dT ∨ dT + 8 * w ≤ dO) :
    WP isa selectAcc64 s fun s' =>
      wordsVal s'.mem B dO w = (if b then wordsVal s.mem B dA w else wordsVal s.mem B dT w) ∧
      Outside B dO (8 * w) s.mem s'.mem ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17] s s' := by
  have hnw := hs.nowrap
  unfold selectAcc64
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r9 0, .addi .r16 .r5 0, .lsr .d .r17 .r11 1]) s
      fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dT ∧ s₁.gpr .r16 = off B dO ∧
        s₁.gpr .r17 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h9, h5, h11, BitVec.add_zero, mont_ofNat_shr1 (show w < 2 ^ 63 by omega_arith)]
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i16, i17, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 8 * i) ∧ t.gpr .r15 = off B (dT + 8 * i) ∧ t.gpr .r16 = off B (dO + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i = (if b then wordsVal s.mem B dA i else wordsVal s.mem B dT i) ∧
      Keep [.r0, .r3, .r14, .r15, .r16, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r15 0, .load .d .r3 .r14 0,
      .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r20, .logic .xor .r3 .r3 .r0, .store .d .r3 .r16 0,
      .addi .r14 .r14 8, .addi .r15 .r15 8, .addi .r16 .r16 8] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j15, j16, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [i16]; rfl, by rw [← im]; exact Outside.refl _ _ _ _,
      by simp only [wordsVal]; split <;> rfl, k₁⟩ i17)
    fun t ⟨_, _, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have r20 : t.gpr .r20 = s.gpr .r20 := jk.gpr _ (by decide)
  have hst : WP isa (.block [.load .d .r0 .r15 0, .load .d .r3 .r14 0, .logic .xor .r3 .r3 .r0,
      .logic .and .r3 .r3 .r20, .logic .xor .r3 .r3 .r0, .store .d .r3 .r16 0, .addi .r14 .r14 8,
      .addi .r15 .r15 8, .addi .r16 .r16 8, .subi .r17 .r17 1]) t fun t' =>
      (t'.gpr .r14 = off B (dA + 8 * i + 8) ∧ t'.gpr .r15 = off B (dT + 8 * i + 8) ∧
        t'.gpr .r16 = off B (dO + 8 * i + 8) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (if b then word t.mem B (dA + 8 * i) else word t.mem B (dT + 8 * i))) ∧
      Keep [.r0, .r3, .r14, .r15, .r16, .r17] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j14, j15, j16, r20, h20, (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dT + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith), select64_arith]
  refine WP.mono hst fun t' ⟨⟨l14, l15, l16, l17, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l17⟩
  · rw [l14, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l15, show dT + 8 * i + 8 = dT + 8 * (i + 1) by omega_arith]
  · rw [l16, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wt : word t.mem B (dT + 8 * i) = word s.mem B (dT + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    rw [lm, fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), jeq, wordsVal_succ_top s.mem B dA i,
      wordsVal_succ_top s.mem B dT i]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [wt]
    · simp only [ite_true]; rw [wa]

/-- `selectAcc64_ok` in `selectAcc_ok`'s terms (`MontFinish.lean`): the `2 w`
digits, and the mask `0 − b`. -/
theorem selectAcc64_ok32 {s : State} {B : Addr} {Z dA dT dO w : Nat} (hs : Scr s B Z) {b : Bool}
    (h8 : s.gpr .r8 = off B dA) (h9 : s.gpr .r9 = off B dT) (h5 : s.gpr .r5 = off B dO)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h20 : s.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) (hn : 1 ≤ 2 * w)
    (hn' : 2 * w < 2 ^ 32) (hA : dA + 4 * (2 * w) ≤ Z) (hT : dT + 4 * (2 * w) ≤ Z) (hO : dO + 4 * (2 * w) ≤ Z)
    (dOA : dO + 4 * (2 * w) ≤ dA ∨ dA + 4 * (2 * w) ≤ dO) (dOT : dO + 4 * (2 * w) ≤ dT ∨ dT + 4 * (2 * w) ≤ dO) :
    WP isa selectAcc64 s fun s' =>
      val32 s'.mem B dO (2 * w) = (if b then val32 s.mem B dA (2 * w) else val32 s.mem B dT (2 * w)) ∧
      Outside B dO (4 * (2 * w)) s.mem s'.mem ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17] s s' := by
  have hm : BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) = if b then BitVec.allOnes 64 else 0 := by
    cases b <;> rfl
  refine WP.mono (selectAcc64_ok (w := w) hs h8 h9 h5 h11 (h20.trans hm) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)) fun s' ⟨hv, hout, k⟩ => ⟨?_, hout.mono (Nat.le_refl _) (by omega), k⟩
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32, ← wordsVal_eq_val32, hv]

end VG.Proof.Bignum.PPC64LE
