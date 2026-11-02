module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Montgomery multiplication on RISC-V: zeroing, and the final subtraction

`zeroAcc_ok`: the accumulator's first `w + 1` words := 0, and the rounds'
count. `subMod64_ok`: `T - m` into the temporary, word by word with the
borrow a bit in `s4` (`sltu`), and the borrow out of the top word as a mask.
`selectAcc64_ok`: the result, `T` or `T - m` by the mask.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64

/-- A store of word `j` of a number of `j + 1` words. -/
theorem fin64_wordsVal_write_top (m : Mem) (B : Addr) (d j : Nat) (v : BitVec 64)
    (h : d + 8 * j + 8 ≤ 2 ^ 64) :
    wordsVal (m.writeW (off B (d + 8 * j)) v) B d (j + 1) = wordsVal m B d j + 2 ^ (64 * j) * v.toNat := by
  rw [wordsVal_succ_top, (writeW_outside m B v h).wordsVal (by omega_arith) (by omega_arith), word_writeW_self]

/-- `li` of a numeral below 2048, as an `Int` literal. -/
theorem fin64_exec_li_lit {s : State} {d : Reg} {m : Nat} (h : m < 2048) :
    exec (.li d (OfNat.ofNat m : Int)) s = some (s.write d (BitVec.ofNat 64 m)) :=
  exec_li_nat h

/-- `li` of 0. -/
theorem fin64_exec_li_zero {s : State} {d : Reg} : exec (.li d 0) s = some (s.write d 0) := by
  rw [exec_li (by decide)]; rfl

/-! ## Zeroing the accumulator -/

/-- `zeroAcc`, with `w` in `t0` and the accumulator at `dA` (`a5`): its
first `w + 1` words 0 and `w` in `a1`. -/
theorem zeroAcc_ok {s : State} {B : Addr} {Z dA w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B dA) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hA8 : dA % 8 = 0)
    (hw : w < 2 ^ 31) (hA : dA + 8 * (w + 1) ≤ Z) :
    WP isa zeroAcc s fun s' =>
      wordsVal s'.mem B dA (w + 1) = 0 ∧ Outside B dA (8 * (w + 1)) s.mem s'.mem ∧
        s'.gpr .a1 = BitVec.ofNat 64 w ∧ Keep [.a1, .t3, .t5, .s0] s s' := by
  have hnw := hs.nowrap
  unfold zeroAcc
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .a1 .t0 0, .addi .t3 .a5 0, .addi .t5 .t0 1, .li .s0 0]) s
      fun s₁ => (s₁.gpr .a1 = BitVec.ofNat 64 w ∧ s₁.gpr .t3 = off B dA ∧
        s₁.gpr .t5 = BitVec.ofNat 64 (w + 1) ∧ s₁.gpr .s0 = 0 ∧ s₁.mem = s.mem) ∧
        Keep [.a1, .t3, .t5, .s0] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, h5, h0, BitVec.add_zero]
    exact (BitVec.ofNat_add _ _).symm
  refine WP.mono hpre fun s₁ ⟨⟨i1, i3, i5, i0, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dA + 8 * i) ∧ t.gpr .s0 = 0 ∧ Outside B dA (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dA i = 0 ∧ Keep [.t3, .t5] s₁ t
  refine WP.mono (wp_countdown (body := .block ([.store .d .s0 .t3 0, .addi .t3 .t3 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w + 1) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j3, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, i0, by rw [← im]; exact Outside.refl _ _ _ _, rfl, Keep.refl _ _⟩ i5)
    fun t ⟨_, _, tout, tz, tk⟩ => ⟨tz, tout, by rw [tk.gpr (by decide)]; exact i1,
      (k₁.trans tk).mono (by decide)⟩
  have hs' := hs.congr (k₁.trans jk).2.2
  have hst : WP isa (.block [.store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t5 .t5 (-1)]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (off B (dA + 8 * i)) (0 : BitVec 64) } : State).write
        .t3 (off B (dA + 8 * i + 8))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1)) := by
    brun [fin64_exec_li_zero, j3, j0, hs'.st (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  refine ⟨⟨by gsimp; rw [show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside t.mem B (d := dA + 8 * i) 0 (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · gsimp
    rw [fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), jz]
    rfl
  · exact Keep.trans' jk ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-! ## The subtraction of `m` -/

/-- A word of a subtraction: `x - y - b` (`b` the borrow in, 0 or 1) is the
low word, and `sltu`'s two borrows, or-ed, the borrow out. -/
theorem sub64_arith (x y b : BitVec 64) (hb : b.toNat ≤ 1) :
    (x - y - b).toNat + y.toNat + b.toNat =
        x.toNat + 2 ^ 64 * (((if x < y then (1 : BitVec 64) else 0) |||
          (if x - y < b then 1 else 0))).toNat ∧
      (((if x < y then (1 : BitVec 64) else 0) ||| (if x - y < b then 1 else 0))).toNat ≤ 1 := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h1 : x < y <;> by_cases h2 : x - y < b <;>
    simp only [h1, h2, ite_true, ite_false] <;>
    rw [BitVec.lt_def] at h1 h2 <;>
    simp only [BitVec.toNat_sub, Nat.not_lt] at h1 h2 ⊢ <;>
    first
    | (exact absurd h2 (by omega_arith))
    | (refine ⟨?_, by decide⟩; simp only [show ((1 : BitVec 64) ||| 0) = 1 from rfl, show ((0 : BitVec 64) ||| 1) = 1 from rfl,
        show ((0 : BitVec 64) ||| 0) = 0 from rfl, show (1 : BitVec 64).toNat = 1 from rfl,
        show (0 : BitVec 64).toNat = 0 from rfl]; omega_arith)

/-- The mask of the top word `t` below the borrow `b`: all ones if `t < b`,
else 0. -/
theorem mask_arith (t b : BitVec 64) :
    BitVec.ofNat 64 0 - (if t < b then (1 : BitVec 64) else 0) =
      if t.toNat < b.toNat then BitVec.allOnes 64 else 0 := by
  by_cases h : t < b
  · have h' : t.toNat < b.toNat := BitVec.lt_def.mp h
    simp only [h, h', ↓reduceIte]; rfl
  · have h' : ¬ t.toNat < b.toNat := fun h' => h (BitVec.lt_def.mpr h')
    simp only [h, h', ↓reduceIte]; rfl

/-- `subMod64`, the accumulator `T` (`w + 1` words) at `dA` (`a5`), the
temporary at `dT` (`a6`) and `m` at `dM` (`a7`): the temporary's first `w`
words are `D` with `D + m = T_L + 2^(64 w) c` (`T_L` the low `w` words of
`T`, `c` the borrow), and `s4` the mask of `t_w < c`, all ones or 0. -/
theorem subMod64_ok {s : State} {B : Addr} {Z dA dT dM w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B dA) (h6 : s.gpr .a6 = off B dT) (h7 : s.gpr .a7 = off B dM)
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hA8 : dA % 8 = 0) (hT8 : dT % 8 = 0) (hM8 : dM % 8 = 0)
    (hA : dA + 8 * (w + 1) ≤ Z) (hT : dT + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dTA : dT + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dT) (dTM : dT + 8 * w ≤ dM ∨ dM + 8 * w ≤ dT) :
    WP isa subMod64 s fun s' =>
      (∃ c ≤ 1, wordsVal s'.mem B dT w + wordsVal s.mem B dM w = wordsVal s.mem B dA w + 2 ^ (64 * w) * c ∧
        s'.gpr .s4 = if (word s.mem B (dA + 8 * w)).toNat < c then BitVec.allOnes 64 else 0) ∧
      Outside B dT (8 * w) s.mem s'.mem ∧ Keep [.a0, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4] s s' := by
  have hnw := hs.nowrap
  unfold subMod64
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t3 .a5 0, .addi .t4 .a6 0, .addi .a0 .a7 0, .addi .t5 .t0 0, .li .s4 0]) s
      fun s₁ => (s₁.gpr .t3 = off B dA ∧ s₁.gpr .t4 = off B dT ∧
        s₁.gpr .a0 = off B dM ∧ s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.gpr .s4 = 0 ∧ s₁.mem = s.mem) ∧
        Keep [.a0, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, h5, h6, h7, h0, BitVec.add_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i3, i4, i0, i5, i4b, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dA + 8 * i) ∧ t.gpr .t4 = off B (dT + 8 * i) ∧ t.gpr .a0 = off B (dM + 8 * i) ∧
      Outside B dT (8 * i) s.mem t.mem ∧ (t.gpr .s4).toNat ≤ 1 ∧
      wordsVal t.mem B dT i + wordsVal s.mem B dM i = wordsVal s.mem B dA i + 2 ^ (64 * i) * (t.gpr .s4).toNat ∧
      Keep [.a0, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .s2 .t3 0, .load .d .s3 .a0 0,
      .sltu .s0 .s2 .s3, .sub .s2 .s2 .s3, .sltu .s1 .s2 .s4, .sub .s2 .s2 .s4, .logic .or .s4 .s0 .s1,
      .store .d .s2 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .a0 .a0 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j3, j4, j0, jout, jb, jeq, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, by rw [i4]; rfl, by rw [i0]; rfl, by rw [← im]; exact Outside.refl _ _ _ _,
      by rw [i4b]; decide, by simp [wordsVal, i4b], k₁⟩ i5)
    fun t ⟨j3, _, _, jout, jb, jeq, jk⟩ => ?_)
  · have hs' := hs.congr jk.2.2
    have hst : WP isa (.block [.load .d .s2 .t3 0, .load .d .s3 .a0 0,
        .sltu .s0 .s2 .s3, .sub .s2 .s2 .s3, .sltu .s1 .s2 .s4, .sub .s2 .s2 .s4, .logic .or .s4 .s0 .s1,
        .store .d .s2 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .a0 .a0 8, .addi .t5 .t5 (-1)]) t fun t' =>
        (t'.gpr .t3 = off B (dA + 8 * i + 8) ∧ t'.gpr .t4 = off B (dT + 8 * i + 8) ∧
          t'.gpr .a0 = off B (dM + 8 * i + 8) ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dT + 8 * i))
            (word t.mem B (dA + 8 * i) - word t.mem B (dM + 8 * i) - t.gpr .s4) ∧
          t'.gpr .s4 = ((if word t.mem B (dA + 8 * i) < word t.mem B (dM + 8 * i) then (1 : BitVec 64) else 0) |||
            (if word t.mem B (dA + 8 * i) - word t.mem B (dM + 8 * i) < t.gpr .s4 then 1 else 0))) ∧
        Keep [.a0, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4] t t' := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [fin64_exec_li_zero, j3, j4, j0, hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
        hs'.ld (show dM + 8 * i + 8 ≤ Z by omega_arith),
        hs'.st (show dT + 8 * i + 8 ≤ Z by omega_arith),
        hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
        hs'.al8 (show dM + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
        hs'.al8 (show dT + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    refine WP.mono hst fun t' ⟨⟨l3, l4, l0, l5, lm, lb⟩, lk⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l5⟩
    · rw [l3, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
    · rw [l4, show dT + 8 * i + 8 = dT + 8 * (i + 1) by omega_arith]
    · rw [l0, show dM + 8 * i + 8 = dM + 8 * (i + 1) by omega_arith]
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW_outside _ B (d := dT + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · rw [lb]; exact (sub64_arith _ _ _ jb).2
    · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) := jout.word (by omega_arith) (by omega_arith)
      have wm : word t.mem B (dM + 8 * i) = word s.mem B (dM + 8 * i) := jout.word (by omega_arith) (by omega_arith)
      have k := (sub64_arith (word t.mem B (dA + 8 * i)) (word t.mem B (dM + 8 * i)) (t.gpr .s4) jb).1
      rw [← lb, wa, wm] at k
      rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dM i,
        wordsVal_succ_top s.mem B dA i, Nat.mul_succ, Nat.pow_add, wa, wm]
      have e : 2 ^ (64 * i) * (word s.mem B (dA + 8 * i) - word s.mem B (dM + 8 * i) - t.gpr .s4).toNat +
          2 ^ (64 * i) * (word s.mem B (dM + 8 * i)).toNat + 2 ^ (64 * i) * (t.gpr .s4).toNat =
          2 ^ (64 * i) * (word s.mem B (dA + 8 * i)).toNat + 2 ^ (64 * i) * 2 ^ 64 * (t'.gpr .s4).toNat := by
        rw [← Nat.mul_add, ← Nat.mul_add, Nat.mul_assoc, ← Nat.mul_add, k]
      grind
  · have hs' := hs.congr jk.2.2
    have hfin : WP isa (.block [.load .d .s2 .t3 0, .sltu .s0 .s2 .s4, .li .s1 0, .sub .s4 .s1 .s0]) t
        fun t' => (t'.gpr .s4 = BitVec.ofNat 64 0 - (if word t.mem B (dA + 8 * w) < t.gpr .s4 then 1 else 0) ∧
          t'.mem = t.mem) ∧ Keep [.s0, .s1, .s2, .s4] t t' := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [fin64_exec_li_zero, j3, hs'.ld (show dA + 8 * w + 8 ≤ Z by omega_arith),
        hs'.al8 (show dA + 8 * w + 8 ≤ Z by omega_arith) (by omega_arith)]
      rfl
    refine WP.mono hfin fun t' ⟨⟨l4, lm⟩, lk⟩ => ⟨⟨(t.gpr .s4).toNat, jb, by rw [lm]; exact jeq, ?_⟩,
      by rw [lm]; exact jout, Keep.trans' jk (lk.mono (by decide))⟩
    have wa : word t.mem B (dA + 8 * w) = word s.mem B (dA + 8 * w) := jout.word (by omega_arith) (by omega_arith)
    rw [l4, mask_arith, wa]

/-! ## The selection -/

/-- A word of the selection. -/
theorem select64_arith (x y : BitVec 64) (b : Bool) :
    ((y ^^^ x) &&& (if b then BitVec.allOnes 64 else 0)) ^^^ x = if b then y else x := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, BitVec.zero_xor]
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- `selectAcc64`, the mask of `b` in `s4`: the `w` words at `o` (`dO`,
`a2`) are those of the accumulator (`dA`, `a5`) if `b`, else the
temporary's (`dT`, `a6`). -/
theorem selectAcc64_ok {s : State} {B : Addr} {Z dA dT dO w : Nat} (hs : Scr s B Z) {b : Bool}
    (h5 : s.gpr .a5 = off B dA) (h6 : s.gpr .a6 = off B dT) (h2 : s.gpr .a2 = off B dO)
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h4 : s.gpr .s4 = if b then BitVec.allOnes 64 else 0) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hA8 : dA % 8 = 0) (hT8 : dT % 8 = 0) (hO8 : dO % 8 = 0)
    (hA : dA + 8 * w ≤ Z) (hT : dT + 8 * w ≤ Z) (hO : dO + 8 * w ≤ Z)
    (dOA : dO + 8 * w ≤ dA ∨ dA + 8 * w ≤ dO) (dOT : dO + 8 * w ≤ dT ∨ dT + 8 * w ≤ dO) :
    WP isa selectAcc64 s fun s' =>
      wordsVal s'.mem B dO w = (if b then wordsVal s.mem B dA w else wordsVal s.mem B dT w) ∧
      Outside B dO (8 * w) s.mem s'.mem ∧ Keep [.a0, .t3, .t4, .t5, .s2, .s3] s s' := by
  have hnw := hs.nowrap
  unfold selectAcc64
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t3 .a5 0, .addi .t4 .a6 0, .addi .a0 .a2 0, .addi .t5 .t0 0]) s
      fun s₁ => (s₁.gpr .t3 = off B dA ∧ s₁.gpr .t4 = off B dT ∧ s₁.gpr .a0 = off B dO ∧
        s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.mem = s.mem) ∧ Keep [.a0, .t3, .t4, .t5, .s2, .s3] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, h5, h6, h2, h0, BitVec.add_zero]
  refine WP.mono hpre fun s₁ ⟨⟨i3, i4, i0, i5, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dA + 8 * i) ∧ t.gpr .t4 = off B (dT + 8 * i) ∧ t.gpr .a0 = off B (dO + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i = (if b then wordsVal s.mem B dA i else wordsVal s.mem B dT i) ∧
      Keep [.a0, .t3, .t4, .t5, .s2, .s3] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s2 .t4 0, .load .d .s3 .t3 0,
      .logic .xor .s3 .s3 .s2, .logic .and .s3 .s3 .s4, .logic .xor .s3 .s3 .s2, .store .d .s3 .a0 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .a0 .a0 8] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j3, j4, j0, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, by rw [i4]; rfl, by rw [i0]; rfl, by rw [← im]; exact Outside.refl _ _ _ _,
      by simp only [wordsVal]; split <;> rfl, k₁⟩ i5)
    fun t ⟨_, _, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have r4 : t.gpr .s4 = s.gpr .s4 := jk.gpr (by decide)
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block [.load .d .s2 .t4 0, .load .d .s3 .t3 0,
      .logic .xor .s3 .s3 .s2, .logic .and .s3 .s3 .s4, .logic .xor .s3 .s3 .s2, .store .d .s3 .a0 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .a0 .a0 8, .addi .t5 .t5 (-1)]) t fun t' =>
      (t'.gpr .t3 = off B (dA + 8 * i + 8) ∧ t'.gpr .t4 = off B (dT + 8 * i + 8) ∧
        t'.gpr .a0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (if b then word t.mem B (dA + 8 * i) else word t.mem B (dT + 8 * i))) ∧
      Keep [.a0, .t3, .t4, .t5, .s2, .s3] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, j3, j4, j0, r4, h4, hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dT + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dT + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith), select64_arith]
  refine WP.mono hst fun t' ⟨⟨l3, l4, l0, l5, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l5⟩
  · rw [l3, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l4, show dT + 8 * i + 8 = dT + 8 * (i + 1) by omega_arith]
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wt : word t.mem B (dT + 8 * i) = word s.mem B (dT + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), jeq, wordsVal_succ_top s.mem B dA i,
      wordsVal_succ_top s.mem B dT i]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [wt]
    · simp only [ite_true]; rw [wa]

end VG.Proof.Bignum.RISCV64
