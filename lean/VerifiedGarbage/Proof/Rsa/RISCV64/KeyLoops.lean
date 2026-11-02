module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyWs
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The word loops of the RSA key operations on RISC-V

Each loop runs over `n` words at byte offsets of the working space
(`Scr s B Z`), multiples of 8, its pointers in `t0`–`t2` and its count in `t3`
(`countLoop .t3 body`), and changes only `loopRegs`:

* `subLoop_ok`: `[o] := [a] - [b]`, the borrow in and out in `t4`;
* `selLoop_ok`: `[o] := mask ? [b] : [a]`, the mask in `t4`;
* `copyLoop_ok`: `[o] := [a]`;
* `eqLoop_ok`: `t4 = 0` exactly when `[a] = [b]`;
* `zeroLoop_ok`: `n` words from `t0` := 0 (`t5 = 0`);
* `halfLoop_ok`: the `n + 1` words at `t0` shifted right by one into the
  low `n`.

The output may be an input, or come before it, or be apart from it
(`Ahead`): a word is read before any word at or after it is written.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Loops

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys

/-- The registers the word loops change. -/
abbrev loopRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4]

/-- Array `a` (at `dA`) is read after `o` (at `dO`) is written up to the
same word: it is `o` or after it, or apart from it. -/
def Ahead (dO dA n : Nat) : Prop := dO ≤ dA ∨ dA + 8 * n ≤ dO

theorem Ahead.outside {dO dA n i : Nat} (h : Ahead dO dA n) (hi : i < n) :
    dA + 8 * i + 8 ≤ dO ∨ dO + 8 * i ≤ dA + 8 * i := by
  unfold Ahead at h; omega_arith

/-- A word of `[o]` written, as the top word of a number of `i + 1` words. -/
theorem out_step {s t : State} {B : Addr} {dO i : Nat} (v : BitVec 64)
    (h : Outside B dO (8 * i) s.mem t.mem) (hnw : dO + 8 * i + 8 ≤ 2 ^ 64) :
    Outside B dO (8 * (i + 1)) s.mem (t.mem.writeW (off B (dO + 8 * i)) v) :=
  (h.mono (Nat.le_refl _) (by omega_arith)).trans
    ((writeW_outside _ B (d := dO + 8 * i) _ hnw).mono (by omega_arith) (by omega_arith))

/-- `[o] := [a] - [b]` over `n` words (`countLoop .t3 subBody`), from the
borrow `c` in `t4`: the difference and the borrow out. -/
theorem subLoop_ok {s : State} {B : Addr} {Z dO dA dB n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dB)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h4 : (s.gpr .t4).toNat ≤ 1) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hA : dA + 8 * n ≤ Z) (hB : dB + 8 * n ≤ Z)
    (aA : Ahead dO dA n) (aB : Ahead dO dB n) :
    WP isa (countLoop .t3 subBody) s fun t =>
      (t.gpr .t4).toNat ≤ 1 ∧
      wordsVal t.mem B dO n + wordsVal s.mem B dB n + (s.gpr .t4).toNat =
        wordsVal s.mem B dA n + 2 ^ (64 * n) * (t.gpr .t4).toNat ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dA + 8 * i) ∧ t.gpr .t2 = off B (dB + 8 * i) ∧
      (t.gpr .t4).toNat ≤ 1 ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + wordsVal s.mem B dB i + (s.gpr .t4).toNat =
        wordsVal s.mem B dA i + 2 ^ (64 * i) * (t.gpr .t4).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (subBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j2, j4, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, h4, Outside.refl _ _ _ _,
      by simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, _, _, j4, jout, jeq, jk⟩ => ⟨j4, jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (subBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dA + 8 * i + 8) ∧
        t'.gpr .t2 = off B (dB + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dA + 8 * i) - word t.mem B (dB + 8 * i) - t.gpr .t4) ∧
        t'.gpr .t4 = ((if word t.mem B (dA + 8 * i) < word t.mem B (dB + 8 * i) then (1 : BitVec 64) else 0) |||
          (if word t.mem B (dA + 8 * i) - word t.mem B (dB + 8 * i) < t.gpr .t4 then 1 else 0))) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [subBody, j0, j1, j2, hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dB + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dB + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l3, lm, lb⟩, lk⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l2, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · rw [lb]; exact (sub64_arith _ _ _ j4).2
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wb : word t.mem B (dB + 8 * i) = word s.mem B (dB + 8 * i) :=
      jout.word (by have := aB.outside hi; omega_arith) (by omega_arith)
    have k := (sub64_arith (word t.mem B (dA + 8 * i)) (word t.mem B (dB + 8 * i)) (t.gpr .t4) j4).1
    rw [← lb, wa, wb] at k
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dB i,
      wordsVal_succ_top s.mem B dA i, Nat.mul_succ, Nat.pow_add, wa, wb]
    have e : 2 ^ (64 * i) * (word s.mem B (dA + 8 * i) - word s.mem B (dB + 8 * i) - t.gpr .t4).toNat +
        2 ^ (64 * i) * (word s.mem B (dB + 8 * i)).toNat + 2 ^ (64 * i) * (t.gpr .t4).toNat =
        2 ^ (64 * i) * (word s.mem B (dA + 8 * i)).toNat + 2 ^ (64 * i) * 2 ^ 64 * (t'.gpr .t4).toNat := by
      rw [← Nat.mul_add, ← Nat.mul_add, Nat.mul_assoc, ← Nat.mul_add, k]
    grind

/-- `[o] := b ? [b] : [a]` over `n` words (`countLoop .t3 selBody`), the
mask of `b` in `t4`. -/
theorem selLoop_ok {s : State} {B : Addr} {Z dO dA dB n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dB)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (h4 : s.gpr .t4 = if b then BitVec.allOnes 64 else 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hA : dA + 8 * n ≤ Z) (hB : dB + 8 * n ≤ Z)
    (aA : Ahead dO dA n) (aB : Ahead dO dB n) :
    WP isa (countLoop .t3 selBody) s fun t =>
      wordsVal t.mem B dO n = (if b then wordsVal s.mem B dB n else wordsVal s.mem B dA n) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t ∧ t.gpr .t4 = s.gpr .t4 := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dA + 8 * i) ∧ t.gpr .t2 = off B (dB + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i = (if b then wordsVal s.mem B dB i else wordsVal s.mem B dA i) ∧
      Keep loopRegs s t ∧ t.gpr .t4 = s.gpr .t4
  refine WP.mono (wp_countdown (body := .block (selBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j2, jout, jeq, jk, j4⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, Outside.refl _ _ _ _,
      by simp only [wordsVal]; split <;> rfl, Keep.refl _ _, rfl⟩ h3)
    fun t ⟨_, _, _, jout, jeq, jk, j4⟩ => ⟨jeq, jout, jk, j4⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (selBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dA + 8 * i + 8) ∧
        t'.gpr .t2 = off B (dB + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.gpr .t4 = t.gpr .t4 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (if b then word t.mem B (dB + 8 * i) else word t.mem B (dA + 8 * i))) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [selBody, j0, j1, j2, j4, h4, hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dB + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dB + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith), select64_arith]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l3, l4, lm⟩, lk⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk, l4.trans j4⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l2, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wb : word t.mem B (dB + 8 * i) = word s.mem B (dB + 8 * i) :=
      jout.word (by have := aB.outside hi; omega_arith) (by omega_arith)
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), jeq, wordsVal_succ_top s.mem B dA i,
      wordsVal_succ_top s.mem B dB i]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; rw [wa]
    · simp only [ite_true]; rw [wb]

/-- `[o] := [a]` over `n` words (`countLoop .t3 copyBody`). -/
theorem copyLoop_ok {s : State} {B : Addr} {Z dO dA n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO8 : dO % 8 = 0) (hA8 : dA % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hA : dA + 8 * n ≤ Z) (aA : Ahead dO dA n) :
    WP isa (countLoop .t3 copyBody) s fun t =>
      wordsVal t.mem B dO n = wordsVal s.mem B dA n ∧ Outside B dO (8 * n) s.mem t.mem ∧
        Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dA + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧ wordsVal t.mem B dO i = wordsVal s.mem B dA i ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (copyBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, Outside.refl _ _ _ _, rfl, Keep.refl _ _⟩ h3)
    fun t ⟨_, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (copyBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dA + 8 * i + 8) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) (word t.mem B (dA + 8 * i))) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [copyBody, j0, j1, hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), jeq, wordsVal_succ_top s.mem B dA i, wa]

/-- Two numbers of a low part below `K` and a high part are equal exactly
when both parts are. -/
theorem split_eq_iff {x y a b K : Nat} (hK : 0 < K) (hx : x < K) (hy : y < K) :
    x + K * a = y + K * b ↔ x = y ∧ a = b := by
  constructor
  · intro h
    have hm := congrArg (· % K) h
    have hd := congrArg (· / K) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hm
    simp only [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy,
      Nat.zero_add] at hd
    exact ⟨hm, hd⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- A word of the comparison, on bit vectors. -/
theorem eq64_arith (r x y : BitVec 64) : r ||| (x ^^^ y) = 0 ↔ r = 0 ∧ x = y := by
  change (r ||| (x ^^^ y)) = 0#64 ↔ r = 0#64 ∧ x = y
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]

/-- Whether `[a] = [b]` over `n` words (`countLoop .t3 eqBody`), from `t4 = 0`:
`t4` is zero exactly when they are equal. -/
theorem eqLoop_ok {s : State} {B : Addr} {Z dA dB n : Nat} (hs : Scr s B Z)
    (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dB) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (h4 : s.gpr .t4 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0)
    (hA : dA + 8 * n ≤ Z) (hB : dB + 8 * n ≤ Z) :
    WP isa (countLoop .t3 eqBody) s fun t =>
      (t.gpr .t4 = 0 ↔ wordsVal s.mem B dA n = wordsVal s.mem B dB n) ∧ t.mem = s.mem ∧
        Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t1 = off B (dA + 8 * i) ∧ t.gpr .t2 = off B (dB + 8 * i) ∧ t.mem = s.mem ∧
      (t.gpr .t4 = 0 ↔ wordsVal s.mem B dA i = wordsVal s.mem B dB i) ∧ Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (eqBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j1, j2, jm, jeq, jk⟩ hc => ?_)
    ⟨by rw [h1]; rfl, by rw [h2]; rfl, rfl, by simp [wordsVal, h4], Keep.refl _ _⟩ h3)
    fun t ⟨_, _, jm, jeq, jk⟩ => ⟨jeq, jm, jk⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (eqBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t1 = off B (dA + 8 * i + 8) ∧ t'.gpr .t2 = off B (dB + 8 * i + 8) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.gpr .t4 = t.gpr .t4 ||| (word t.mem B (dA + 8 * i) ^^^ word t.mem B (dB + 8 * i)) ∧
        t'.mem = t.mem) ∧ Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [eqBody, j1, j2, hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dB + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dB + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l1, l2, l3, l4, lm⟩, lk⟩ => ⟨⟨?_, ?_, lm.trans jm, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l1, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l2, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · rw [l4, eq64_arith, jeq, jm, wordsVal_succ_top s.mem B dA i, wordsVal_succ_top s.mem B dB i,
      split_eq_iff (Nat.two_pow_pos _) (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)]
    exact and_congr_right fun _ => ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩

/-- `n` words from `t0` (at `dO`) := 0 (`countLoop .t3 [sd t5, 0(t0); addi t0, t0, 8]`, `t5 = 0`). -/
theorem zeroLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h5 : s.gpr .t5 = 0)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO8 : dO % 8 = 0) (hO : dO + 8 * n ≤ Z) :
    WP isa (countLoop .t3 [.store .d .t5 .t0 0, .addi .t0 .t0 8]) s fun t =>
      wordsVal t.mem B dO n = 0 ∧ Outside B dO (8 * n) s.mem t.mem ∧ Keep [.t0, .t3] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i = 0 ∧ Keep [.t0, .t3] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .t5 .t0 0, .addi .t0 .t0 8] ++
      ([.addi .t3 .t3 (-1)] : List Instr))) (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, Outside.refl _ _ _ _, rfl, Keep.refl _ _⟩ h3)
    fun t ⟨_, jout, jz, jk⟩ => ⟨jz, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have t5 : t.gpr .t5 = 0 := (jk.gpr (by decide)).trans h5
  have hst : WP isa (.block [.store .d .t5 .t0 0, .addi .t0 .t0 8, .addi .t3 .t3 (-1)]) t
      fun t' => (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) (0 : BitVec 64)) ∧ Keep [.t0, .t3] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [j0, t5, hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), jz]; rfl

/-- A word of the halving: the upper 63 bits of `x` and the low bit of `y`. -/
theorem half64_arith (x y : BitVec 64) :
    2 * ((x >>> 1 ||| y <<< 63).toNat) + x.toNat % 2 = x.toNat + 2 ^ 64 * (y.toNat % 2) := by
  have e : (x >>> 1 ||| y <<< 63).toNat = x.toNat / 2 + 2 ^ 63 * (y.toNat % 2) := by
    have h1 : (x >>> 1).toNat = x.toNat / 2 := by rw [BitVec.toNat_ushiftRight]; rfl
    have h2 : (y <<< 63).toNat = 2 ^ 63 * (y.toNat % 2) := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      have := y.isLt
      omega_arith
    have hd : x >>> 1 &&& y <<< 63 = 0 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
      by_cases h : i < 63
      · simp [h]
      · have : i = 63 := by omega
        subst this
        simp
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
    have := x.isLt
    omega_arith
  rw [e]; have := x.isLt; omega_arith

/-- The halving over `n` words at `t0` (`countLoop .t3 halfBody`): word `i`
:= the upper 63 bits of word `i` and the low bit of word `i + 1`, so that the
`n` words are the `n + 1` words halved. -/
theorem halfLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hO : dO + 8 * (n + 1) ≤ Z) :
    WP isa (countLoop .t3 halfBody) s fun t =>
      2 * wordsVal t.mem B dO n + (word s.mem B dO).toNat % 2 =
        wordsVal s.mem B dO n + 2 ^ (64 * n) * ((word s.mem B (dO + 8 * n)).toNat % 2) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      2 * wordsVal t.mem B dO i + (word s.mem B dO).toNat % 2 =
        wordsVal s.mem B dO i + 2 ^ (64 * i) * ((word s.mem B (dO + 8 * i)).toNat % 2) ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (halfBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (halfBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dO + 8 * i) >>> 1 ||| word t.mem B (dO + 8 * i + 8) <<< 63)) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [halfBody, j0, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dO + 8 * i + 8 + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wb : word t.mem B (dO + 8 * i + 8) = word s.mem B (dO + 8 * i + 8) :=
      jout.word (by omega_arith) (by omega_arith)
    have k := half64_arith (word s.mem B (dO + 8 * i)) (word s.mem B (dO + 8 * i + 8))
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wa, wb, wordsVal_succ_top s.mem B dO i,
      show dO + 8 * (i + 1) = dO + 8 * i + 8 by omega_arith, Nat.mul_succ, Nat.pow_add]
    have e : 2 * (2 ^ (64 * i) * (word s.mem B (dO + 8 * i) >>> 1 ||| word s.mem B (dO + 8 * i + 8) <<< 63).toNat) +
        2 ^ (64 * i) * ((word s.mem B (dO + 8 * i)).toNat % 2) =
        2 ^ (64 * i) * (word s.mem B (dO + 8 * i)).toNat +
          2 ^ (64 * i) * 2 ^ 64 * ((word s.mem B (dO + 8 * i + 8)).toNat % 2) := by
      rw [Nat.mul_left_comm, ← Nat.mul_add, k, Nat.mul_add, Nat.mul_assoc]
    grind

end VG.Proof.Rsa.RISCV64.Loops
