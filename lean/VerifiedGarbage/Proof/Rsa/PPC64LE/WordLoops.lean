module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Div
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The word loops of the RSA key operations on PPC64LE

As `Loops.lean`'s digit loops, over `m` words of 64 bits (`wordsVal`), for
the arrays of an even number of digits:

* `subWLoop_ok`: `[o] := [a] - [b]`, the borrow chained through the carry bit
  (set for no borrow);
* `selWLoop_ok`: `[o] := mask ? [b] : [a]`;
* `copyWLoop_ok`: `[o] := [a]`;
* `eqWLoop_ok`: `r9 |= [a] ^ [b]`;
* `halfWLoop_ok`: `[o] := ([o] + bit · 2^(64 m)) / 2`, the bit the low bit of
  the digit after the words;
* `shlWLoop_ok`: `[o] := 2 [o] + r9`, the carry out in `r9`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Loops

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Rsa.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys

/-- Array `a` (at `dA`) is read after `o` (at `dO`) is written up to the
same word: it is `o` or after it, or apart from it. -/
def AheadW (dO dA m : Nat) : Prop := dO ≤ dA ∨ dA + 8 * m ≤ dO

theorem AheadW.outside {dO dA m i : Nat} (h : AheadW dO dA m) (hi : i < m) :
    dA + 8 * i + 8 ≤ dO ∨ dO + 8 * i ≤ dA + 8 * i := by
  unfold AheadW at h; omega

theorem wordsVal_write_top (m : Mem) (B : Addr) (d i : Nat) (v : BitVec 64) (h : d + 8 * i + 8 ≤ 2 ^ 64) :
    wordsVal (m.writeW (off B (d + 8 * i)) v) B d (i + 1) = wordsVal m B d i + 2 ^ (64 * i) * v.toNat := by
  rw [wordsVal_succ_top, (writeW_outside m B v h).wordsVal (by omega) (by omega), word_writeW_self]

theorem pow64_mul (i : Nat) : 2 ^ 64 * 2 ^ (64 * i) = 2 ^ (64 * (i + 1)) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- A word of the subtraction: `a - b - (1 - c)`, its carry clear for a borrow. -/
theorem subW_arith (a b c : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c ≤ 1) :
    (a + (2 ^ 64 - 1 - b) + c) % 2 ^ 64 + b + (1 - c) =
      a + 2 ^ 64 * (1 - (decide (2 ^ 64 ≤ a + (2 ^ 64 - 1 - b) + c)).toNat) := by
  by_cases h : 2 ^ 64 ≤ a + (2 ^ 64 - 1 - b) + c
  · simp only [h, decide_true, Bool.toNat_true]
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [h, decide_false, Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `[o] := [a] - [b]` over `m` words (`countLoop .r8 subWBody`), from the
carry `c` (clear for a borrow in): the difference and the carry out. -/
theorem subWLoop_ok {s : State} {B : Addr} {Z dO dA dB m : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 m) (hm : 1 ≤ m) (hm' : m < 2 ^ 32)
    (hO : dO + 8 * m ≤ Z) (hA : dA + 8 * m ≤ Z) (hB : dB + 8 * m ≤ Z)
    (aA : AheadW dO dA m) (aB : AheadW dO dB m) :
    WP isa (countLoop .r8 subWBody) s fun t =>
      wordsVal t.mem B dO m + wordsVal s.mem B dB m + (1 - s.ca.toNat) =
        wordsVal s.mem B dA m + 2 ^ (64 * m) * (1 - t.ca.toNat) ∧
      Outside B dO (8 * m) s.mem t.mem ∧ Keep loopRegs s t ∧
      t.gpr .r5 = off B (dO + 8 * m) ∧ t.gpr .r6 = off B (dA + 8 * m) ∧ t.gpr .r7 = off B (dB + 8 * m) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ t.gpr .r6 = off B (dA + 8 * i) ∧ t.gpr .r7 = off B (dB + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + wordsVal s.mem B dB i + (1 - s.ca.toNat) =
        wordsVal s.mem B dA i + 2 ^ (64 * i) * (1 - t.ca.toNat) ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (subWBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, j7, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl, Outside.refl _ _ _ _,
      by simp [wordsVal], Keep.refl _ _⟩ h8)
    fun t ⟨j5, j6, j7, jout, jeq, jk⟩ => ⟨jeq, jout, jk, j5, j6, j7⟩
  have hst := (show WP isa (.block (subWBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧ t'.gpr .r6 = off B (dA + 8 * i + 8) ∧
        t'.gpr .r7 = off B (dB + 8 * i + 8) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.ca = decide (2 ^ 64 ≤ (word t.mem B (dA + 8 * i)).toNat +
          (2 ^ 64 - 1 - (word t.mem B (dB + 8 * i)).toNat) + t.ca.toNat) ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) (BitVec.ofNat 64 ((word t.mem B (dA + 8 * i)).toNat +
          (2 ^ 64 - 1 - (word t.mem B (dB + 8 * i)).toNat) + t.ca.toNat))) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by decide)
    mcrun [subWBody, j5, j6, j7, exec_load_d, exec_store_d,
      (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dB + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l8, lc, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l6, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l7, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wb : word t.mem B (dB + 8 * i) = word s.mem B (dB + 8 * i) :=
      jout.word (by have := aB.outside hi; omega_arith) (by omega_arith)
    have k := subW_arith (word t.mem B (dA + 8 * i)).toNat (word t.mem B (dB + 8 * i)).toNat t.ca.toNat
      (BitVec.isLt _) (BitVec.isLt _) (by cases t.ca <;> decide)
    rw [lm, lc, wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dB i,
      wordsVal_succ_top s.mem B dA i, ← pow64_mul i, BitVec.toNat_ofNat]
    rw [wa, wb] at k ⊢
    generalize 2 ^ (64 * i) = P at *
    grind

/-- A word of the selection, on bit vectors. -/
theorem selectW_arith (x y : BitVec 64) (b : Bool) :
    ((y ^^^ x) &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))) ^^^ x = if b then y else x := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, BitVec.sub_zero, BitVec.and_zero, BitVec.zero_xor]
  · simp only [↓reduceIte]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- `[o] := b ? [b] : [a]` over `m` words (`countLoop .r8 selWBody`), the
mask of `b` in `r9`. -/
theorem selWLoop_ok {s : State} {B : Addr} {Z dO dA dB m : Nat} (hs : Scr s B Z) {b : Bool}
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 m)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) (hm : 1 ≤ m)
    (hm' : m < 2 ^ 32) (hO : dO + 8 * m ≤ Z) (hA : dA + 8 * m ≤ Z) (hB : dB + 8 * m ≤ Z)
    (aA : AheadW dO dA m) (aB : AheadW dO dB m) :
    WP isa (countLoop .r8 selWBody) s fun t =>
      wordsVal t.mem B dO m = (if b then wordsVal s.mem B dB m else wordsVal s.mem B dA m) ∧
      Outside B dO (8 * m) s.mem t.mem ∧ Keep selRegs s t ∧
      t.gpr .r5 = off B (dO + 8 * m) ∧ t.gpr .r6 = off B (dA + 8 * m) ∧ t.gpr .r7 = off B (dB + 8 * m) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ t.gpr .r6 = off B (dA + 8 * i) ∧ t.gpr .r7 = off B (dB + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i = (if b then wordsVal s.mem B dB i else wordsVal s.mem B dA i) ∧
      Keep selRegs s t
  refine WP.mono (wp_countdown (body := .block (selWBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, j7, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl, Outside.refl _ _ _ _,
      by simp only [wordsVal]; split <;> rfl, Keep.refl _ _⟩ h8)
    fun t ⟨j5, j6, j7, jout, jeq, jk⟩ => ⟨jeq, jout, jk, j5, j6, j7⟩
  have r9 : t.gpr .r9 = s.gpr .r9 := jk.gpr _ (by decide)
  have hst : WP isa (.block (selWBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧ t'.gpr .r6 = off B (dA + 8 * i + 8) ∧
        t'.gpr .r7 = off B (dB + 8 * i + 8) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (if b then word t.mem B (dB + 8 * i) else word t.mem B (dA + 8 * i))) ∧
      Keep selRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [selWBody, j5, j6, j7, r9, h9, (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dB + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith), selectW_arith]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l6, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l7, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wb : word t.mem B (dB + 8 * i) = word s.mem B (dB + 8 * i) :=
      jout.word (by have := aB.outside hi; omega_arith) (by omega_arith)
    rw [lm, wordsVal_write_top _ _ _ _ _ (by omega_arith), jeq, wordsVal_succ_top s.mem B dA i,
      wordsVal_succ_top s.mem B dB i]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [← wa]
    · simp only [ite_true]; rw [← wb]

/-- `[o] := [a]` over `m` words (`countLoop .r8 copyWBody`). -/
theorem copyWLoop_ok {s : State} {B : Addr} {Z dO dA m : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h8 : s.gpr .r8 = BitVec.ofNat 64 m)
    (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hO : dO + 8 * m ≤ Z) (hA : dA + 8 * m ≤ Z) (aA : AheadW dO dA m) :
    WP isa (countLoop .r8 copyWBody) s fun t =>
      wordsVal t.mem B dO m = wordsVal s.mem B dA m ∧ Outside B dO (8 * m) s.mem t.mem ∧
      Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ t.gpr .r6 = off B (dA + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧ wordsVal t.mem B dO i = wordsVal s.mem B dA i ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (copyWBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, Outside.refl _ _ _ _, rfl, Keep.refl _ _⟩ h8)
    fun t ⟨_, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hst : WP isa (.block (copyWBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧ t'.gpr .r6 = off B (dA + 8 * i + 8) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) (word t.mem B (dA + 8 * i))) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [copyWBody, j5, j6, (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l6, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
    rw [lm, wordsVal_write_top _ _ _ _ _ (by omega_arith), jeq, wordsVal_succ_top s.mem B dA i, ← wa]

/-- Whether `[a] = [b]` over `m` words (`countLoop .r8 eqWBody`), from `r9 = 0`:
`r9` is zero exactly when they are equal. -/
theorem eqWLoop_ok {s : State} {B : Addr} {Z dA dB m : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB) (h8 : s.gpr .r8 = BitVec.ofNat 64 m)
    (h9 : s.gpr .r9 = 0) (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hA : dA + 8 * m ≤ Z) (hB : dB + 8 * m ≤ Z) :
    WP isa (countLoop .r8 eqWBody) s fun t =>
      (t.gpr .r9 = 0 ↔ wordsVal s.mem B dA m = wordsVal s.mem B dB m) ∧ t.mem = s.mem ∧
      Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r6 = off B (dA + 8 * i) ∧ t.gpr .r7 = off B (dB + 8 * i) ∧ t.mem = s.mem ∧
      (t.gpr .r9 = 0 ↔ wordsVal s.mem B dA i = wordsVal s.mem B dB i) ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (eqWBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j6, j7, jm, jeq, jk⟩ hc => ?_)
    ⟨by rw [h6]; rfl, by rw [h7]; rfl, rfl, by simp [wordsVal, h9], Keep.refl _ _⟩ h8)
    fun t ⟨_, _, jm, jeq, jk⟩ => ⟨jeq, jm, jk⟩
  have hst : WP isa (.block (eqWBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r6 = off B (dA + 8 * i + 8) ∧ t'.gpr .r7 = off B (dB + 8 * i + 8) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.gpr .r9 = t.gpr .r9 ||| (word t.mem B (dA + 8 * i) ^^^ word t.mem B (dB + 8 * i)) ∧
        t'.mem = t.mem) ∧ Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [eqWBody, j6, j7, (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dB + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l6, l7, l8, l9, lm⟩, lk⟩ => ⟨⟨?_, ?_, lm.trans jm, ?_, jk.trans' lk⟩, l8⟩
  · rw [l6, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l7, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · rw [l9, jm, wordsVal_succ_top s.mem B dA i, wordsVal_succ_top s.mem B dB i,
      split_eq_iff (Nat.two_pow_pos _) (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)]
    change (_ ||| _) = 0#64 ↔ _
    rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, ← jeq]
    exact and_congr_right fun _ => ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩

/-- A word of the halving, on bit vectors. -/
theorem halfW_arith (x : BitVec 64) (y : BitVec 32) :
    ((x >>> 1) ||| (y.setWidth 64 <<< 63)).toNat = x.toNat / 2 + 2 ^ 63 * (y.toNat % 2) := by
  have hx := x.isLt
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, toNat_ext32,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.or_comm,
    show y.toNat * 2 ^ 63 % 2 ^ 64 = 2 ^ 63 * (y.toNat % 2) by omega_arith,
    ← Nat.two_pow_add_eq_or_of_lt (show x.toNat / 2 ^ 1 < 2 ^ 63 by omega_arith)]
  omega_arith

/-- The halving of the `m` words at `dO`, with the low bit of the digit after
them as the top bit. -/
theorem halfWLoop_ok {s : State} {B : Addr} {Z dO m : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h8 : s.gpr .r8 = BitVec.ofNat 64 m) (hm : 1 ≤ m) (hm' : m < 2 ^ 32)
    (hO : dO + 8 * m + 4 ≤ Z) :
    WP isa (countLoop .r8 halfWBody) s fun t =>
      2 * wordsVal t.mem B dO m + w32 s.mem B dO % 2 =
        wordsVal s.mem B dO m + 2 ^ (64 * m) * (w32 s.mem B (dO + 8 * m) % 2) ∧
      Outside B dO (8 * m) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      2 * wordsVal t.mem B dO i + w32 s.mem B dO % 2 =
        wordsVal s.mem B dO i + 2 ^ (64 * i) * (w32 s.mem B (dO + 8 * i) % 2) ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (halfWBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h8)
    fun t ⟨_, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hst : WP isa (.block (halfWBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          ((word t.mem B (dO + 8 * i) >>> 1) ||| ((t.mem.readW (off B (dO + 8 * i + 8)) 32).setWidth 64 <<< 63))) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [halfWBody, j5, (hs.congr jk.wr).ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dO + 8 * i + 8 + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have w0 : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) :=
      jout.word (by omega_arith) (by omega_arith)
    have w1 : w32 t.mem B (dO + 8 * i + 8) = w32 s.mem B (dO + 8 * (i + 1)) := by
      rw [show dO + 8 * (i + 1) = dO + 8 * i + 8 by omega_arith]
      exact jout.w32 (by omega_arith) (by omega_arith)
    have lo : (word s.mem B (dO + 8 * i)).toNat % 2 = w32 s.mem B (dO + 8 * i) % 2 := by
      rw [word_eq_w32]; omega
    have k := halfW_arith (word t.mem B (dO + 8 * i)) (t.mem.readW (off B (dO + 8 * i + 8)) 32)
    rw [lm, wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dO i, ← pow64_mul i, k]
    simp only [w32] at w1 lo jeq ⊢
    rw [w0, w1]
    have hX := Nat.mod_add_div (word s.mem B (dO + 8 * i)).toNat 2
    generalize 2 ^ (64 * i) = P at *
    grind

/-- A word of the left shift, on bit vectors: the word and the carry. -/
theorem shlW_arith (x c : BitVec 64) (hc : c.toNat ≤ 1) :
    ((x <<< 1) ||| c).toNat + 2 ^ 64 * (x >>> 63).toNat = 2 * x.toNat + c.toNat ∧ (x >>> 63).toNat ≤ 1 := by
  have hx := x.isLt
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, show x.toNat * 2 ^ 1 % 2 ^ 64 = 2 ^ 1 * (x.toNat % 2 ^ 63) by omega_arith,
    ← Nat.two_pow_add_eq_or_of_lt (show c.toNat < 2 ^ 1 by omega_arith)]
  omega_arith

/-- The left shift of the `m` words at `dO`, the carry in and out in `r9`. -/
theorem shlWLoop_ok {s : State} {B : Addr} {Z dO m : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h8 : s.gpr .r8 = BitVec.ofNat 64 m) (h9 : (s.gpr .r9).toNat ≤ 1)
    (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hO : dO + 8 * m ≤ Z) :
    WP isa (countLoop .r8 Div.shlWBody) s fun t =>
      (t.gpr .r9).toNat ≤ 1 ∧
      wordsVal t.mem B dO m + 2 ^ (64 * m) * (t.gpr .r9).toNat = 2 * wordsVal s.mem B dO m + (s.gpr .r9).toNat ∧
      Outside B dO (8 * m) s.mem t.mem ∧ Keep loopRegs s t ∧ t.gpr .r5 = off B (dO + 8 * m) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ (t.gpr .r9).toNat ≤ 1 ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .r9).toNat = 2 * wordsVal s.mem B dO i + (s.gpr .r9).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (Div.shlWBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j9, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, h9, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h8)
    fun t ⟨j5, j9, jout, jeq, jk⟩ => ⟨j9, jeq, jout, jk, j5⟩
  have hst : WP isa (.block (Div.shlWBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.gpr .r9 = word t.mem B (dO + 8 * i) >>> 63 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) ((word t.mem B (dO + 8 * i) <<< 1) ||| t.gpr .r9)) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [Div.shlWBody, j5, (hs.congr jk.wr).ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l8, l9, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l9]; exact (shlW_arith _ _ j9).2
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have w0 : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) :=
      jout.word (by omega_arith) (by omega_arith)
    have k := (shlW_arith (word t.mem B (dO + 8 * i)) _ j9).1
    rw [lm, l9, wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dO i, ← pow64_mul i]
    rw [w0] at k ⊢
    generalize 2 ^ (64 * i) = P at *
    grind

end VG.Proof.Rsa.PPC64LE.Loops
