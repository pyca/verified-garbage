module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.WordLoops
public import VerifiedGarbage.Impl.Rsa.PPC64LE.RecoverDet
public import VerifiedGarbage.Proof.Bignum.ShiftStages
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdOps
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Divstep.WordArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdEntry
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: shifts by a count

`RecoverDet.shlBy` and `shrBy` shift a wide array's `L` words by a count of
words and bits, by stages that bit `k` of the count selects (`ShiftStages`):

* the arithmetic of a number's words, of a word of a shift by `b` bits (a
  funnel of two words, `funnel_val`), and of the masks;
* the stages' loops: by `s` words up or down (`shlWords_ok`, `shrWords_ok`),
  and by `b` bits (`shlBits_ok`, `shrBits_ok`), each under a mask;
* the stages in turn (`shlBy_ok`, `shrBy_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RdShift

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (countLoop ptr seqs)
open VG.Proof.Rsa.KeyWorkspace (slot)

/-! ## Arithmetic -/

/-- A number's low `a` words and the `b` above them. -/
theorem wordsVal_append (m : Mem) (B : Addr) (d a b : Nat) :
    wordsVal m B d (a + b) = wordsVal m B d a + 2 ^ (64 * a) * wordsVal m B (d + 8 * a) b := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, Nat.mul_add, val32_append,
    show 32 * (2 * a) = 64 * a by omega, show d + 4 * (2 * a) = d + 8 * a by omega]

/-- A number's lowest word and the rest. -/
theorem wordsVal_succ_low (m : Mem) (B : Addr) (d k : Nat) :
    wordsVal m B d (k + 1) = (word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) k := rfl

/-- Bit `k` of `n`, by its `and` with `2^k`. -/
theorem and_pow_eq_zero_iff (n k : Nat) : n &&& 2 ^ k = 0 ↔ n / 2 ^ k % 2 = 0 := by
  constructor
  · intro h
    have := congrArg (fun x => x.testBit k) h
    simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.and_true, Nat.zero_testBit] at this
    rw [Nat.testBit_eq_decide_div_mod_eq] at this
    simpa using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases e : k = i
    · subst e; rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h]
    · simp [e]

theorem shr63_ofNat (y : BitVec 64) : y >>> 63 = BitVec.ofNat 64 (y.toNat / 2 ^ 63) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have := y.isLt; omega)

/-- `(x | -x) >>> 63` is 1 exactly where `x` is not zero. -/
theorem nz_bit (x : BitVec 64) : (x ||| (0#64 - x)) >>> 63 = BitVec.ofNat 64 (if x = 0#64 then 0 else 1) := by
  by_cases hx : x = 0#64
  · subst hx; decide
  · have hx' : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    simp only [hx, ↓reduceIte]
    rw [BitVec.ushiftRight_or_distrib, shr63_ofNat, shr63_ofNat (y := 0#64 - x), BitVec.toNat_sub,
      show (0#64).toNat = 0 from rfl, Nat.add_zero]
    have hl := x.isLt
    generalize x.toNat = b at hl hx'
    rcases (show b < 2 ^ 63 ∨ 2 ^ 63 ≤ b by omega) with h | h
    · rw [show (2 ^ 64 - b) % 2 ^ 64 / 2 ^ 63 = 1 by omega, show b / 2 ^ 63 = 0 by omega]; decide
    · rw [show b / 2 ^ 63 = 1 by omega]
      rcases (show (2 ^ 64 - b) % 2 ^ 64 / 2 ^ 63 = 0 ∨ (2 ^ 64 - b) % 2 ^ 64 / 2 ^ 63 = 1 by omega) with
        e | e <;> rw [e] <;> decide

/-- The complement of a bit's mask, `bit - 1`, clears where the bit is set. -/
theorem and_compl (x : BitVec 64) (c : Bool) :
    x &&& (BitVec.ofNat 64 (if c then 1 else 0) - BitVec.ofNat 64 1) = if c then 0#64 else x := by
  cases c
  · simp only [Bool.false_eq_true, ite_false]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
  · simp only [ite_true]
    rw [show BitVec.ofNat 64 1 - BitVec.ofNat 64 1 = 0#64 from rfl, BitVec.and_zero]

/-- A word of a shift by `c` bits: the high `64 - c` bits of `x` and the low `c` of `y`
(disjoint, so added). -/
theorem funnel_val (x y : BitVec 64) {c : Nat} (hc : 0 < c) (hc' : c < 64) :
    (x >>> c + y <<< (64 - c)).toNat = x.toNat / 2 ^ c + 2 ^ (64 - c) * (y.toNat % 2 ^ c) := by
  have hP : 2 ^ c * 2 ^ (64 - c) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : (x >>> c).toNat = x.toNat / 2 ^ c := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (y <<< (64 - c)).toNat = 2 ^ (64 - c) * (y.toNat % 2 ^ c) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ← hP, Nat.mul_mod_mul_right, Nat.mul_comm]
  rw [BitVec.toNat_add, h1, h2]
  apply Nat.mod_eq_of_lt
  have a1 : x.toNat / 2 ^ c < 2 ^ (64 - c) := Nat.div_lt_of_lt_mul (by rw [hP]; exact x.isLt)
  have a2 : y.toNat % 2 ^ c + 1 ≤ 2 ^ c := Nat.mod_lt _ (Nat.two_pow_pos _)
  have a3 := Nat.mul_le_mul_left (2 ^ (64 - c)) a2
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (2 ^ (64 - c)) (2 ^ c), hP] at a3
  omega

/-- `(A + 2^b K) / 2^b = A / 2^b + K`. -/
theorem add_pow_mul_div (A K b : Nat) : (A + 2 ^ b * K) / 2 ^ b = A / 2 ^ b + K := by
  rw [Nat.mul_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos b)]

/-- The right shift by `b` bits, a word on: with `N + 2^(64 i) ⌊x / 2^b⌋ = ⌊P / 2^b⌋` for the
low `i + 1` words `P` (`x` the last), the next word `y`'s low `b` bits complete word `i`. -/
theorem shrB_step {N P x y i b : Nat} (hb : b ≤ 64) (h : N + 2 ^ (64 * i) * (x / 2 ^ b) = P / 2 ^ b) :
    N + 2 ^ (64 * i) * (x / 2 ^ b + 2 ^ (64 - b) * (y % 2 ^ b)) + 2 ^ (64 * (i + 1)) * (y / 2 ^ b) =
      (P + 2 ^ (64 * (i + 1)) * y) / 2 ^ b := by
  have e1 : 2 ^ (64 * (i + 1)) = 2 ^ b * (2 ^ (64 * i) * 2 ^ (64 - b)) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  rw [e1, Nat.mul_assoc (2 ^ b) _ y, add_pow_mul_div, ← h]
  have hy := Nat.div_add_mod y (2 ^ b)
  generalize 2 ^ (64 * i) = A at *
  generalize 2 ^ (64 - b) = C at *
  generalize y / 2 ^ b = q at *
  generalize y % 2 ^ b = r at *
  subst hy
  grind

/-- The left shift by `b` bits, a word on from the top: the new top `k` words are
`(Q 2^b + ⌊z / 2^(64 - b)⌋) mod 2^(64 k)` for the old top `k` words `Q` and the word `z` below
them; the word below takes `z`'s low `64 - b` bits and the high `b` of the word `y` below it. -/
theorem shlB_step {S Q z y k b : Nat} (hb : 0 < b) (hb' : b < 64) (hy : y < 2 ^ 64)
    (h : S = (Q * 2 ^ b + z / 2 ^ (64 - b)) % 2 ^ (64 * k)) :
    (y / 2 ^ (64 - b) + 2 ^ b * (z % 2 ^ (64 - b))) + 2 ^ 64 * S =
      ((z + 2 ^ 64 * Q) * 2 ^ b + y / 2 ^ (64 - b)) % 2 ^ (64 * (k + 1)) := by
  have hP : 2 ^ b * 2 ^ (64 - b) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  have hzs := Nat.div_add_mod z (2 ^ (64 - b))
  -- `z 2^b = 2^b (z mod 2^(64 - b)) + 2^64 ⌊z / 2^(64 - b)⌋`.
  have hz2 : z * 2 ^ b = 2 ^ b * (z % 2 ^ (64 - b)) + 2 ^ 64 * (z / 2 ^ (64 - b)) := by
    conv => lhs; rw [← hzs]
    rw [← hP]
    generalize z / 2 ^ (64 - b) = q
    generalize z % 2 ^ (64 - b) = r
    rw [Nat.add_mul, Nat.mul_comm (2 ^ (64 - b) * q), Nat.mul_assoc, Nat.mul_comm r, Nat.mul_comm (2 ^ (64 - b)) q,
      Nat.mul_comm (2 ^ b) (q * 2 ^ (64 - b)), Nat.mul_assoc q]
    omega
  have lo : y / 2 ^ (64 - b) + 2 ^ b * (z % 2 ^ (64 - b)) < 2 ^ 64 := by
    have a1 : y / 2 ^ (64 - b) < 2 ^ b := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, hP]; exact hy)
    have a2 : z % 2 ^ (64 - b) + 1 ≤ 2 ^ (64 - b) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have a3 := Nat.mul_le_mul_left (2 ^ b) a2
    rw [Nat.mul_add, Nat.mul_one, hP] at a3
    omega
  have e : (z + 2 ^ 64 * Q) * 2 ^ b + y / 2 ^ (64 - b) =
      (y / 2 ^ (64 - b) + 2 ^ b * (z % 2 ^ (64 - b))) + 2 ^ 64 * (Q * 2 ^ b + z / 2 ^ (64 - b)) := by
    rw [Nat.add_mul, hz2, Nat.mul_assoc, Nat.mul_add (2 ^ 64)]
    omega
  rw [e, show 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) by rw [← Nat.pow_add]; congr 1; omega,
    VG.Proof.Divstep.WordArith.mod_split lo, h]

/-! ## The word loops -/

open VG.Proof.Rsa.PPC64LE.Loops (selectW_arith wordsVal_write_top)

/-- The mask of a bit, and its complement. -/
abbrev maskOf (c : Bool) : BitVec 64 := BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0)
abbrev complOf (c : Bool) : BitVec 64 := BitVec.ofNat 64 (if c then 1 else 0) - BitVec.ofNat 64 1

/-- The registers of the word loops. -/
abbrev wlRegs : List Reg := [.r0, .r3, .r5, .r6, .r8]

/-- Up the words: `[dO + 8 i] := c ? [dA + 8 i] : [dO + 8 i]` for `i < m`, `dA` ahead of `dO`. -/
theorem selUpLoop_ok {s : State} {B : Addr} {Z dO dA m : Nat} (hs : Scr s B Z) {c : Bool}
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h8 : s.gpr .r8 = BitVec.ofNat 64 m)
    (h9 : s.gpr .r9 = maskOf c) (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hA : dA + 8 * m ≤ Z) (ahead : dO ≤ dA) :
    WP isa (countLoop .r8 [.load .d .r0 .r5 0, .load .d .r3 .r6 0, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
      .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0, .addi .r5 .r5 8, .addi .r6 .r6 8]) s fun t =>
      wordsVal t.mem B dO m = (if c then wordsVal s.mem B dA m else wordsVal s.mem B dO m) ∧
      Outside B dO (8 * m) s.mem t.mem ∧ Keep wlRegs s t ∧ t.gpr .r5 = off B (dO + 8 * m) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ t.gpr .r6 = off B (dA + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i = (if c then wordsVal s.mem B dA i else wordsVal s.mem B dO i) ∧ Keep wlRegs s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, Outside.refl _ _ _ _, by simp only [wordsVal]; split <;> rfl, Keep.refl _ _⟩ h8)
    fun t ⟨j5, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk, j5⟩
  have r9 : t.gpr .r9 = s.gpr .r9 := jk.gpr _ (by decide)
  have hst : WP isa (.block ([.load .d .r0 .r5 0, .load .d .r3 .r6 0, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
      .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0, .addi .r5 .r5 8, .addi .r6 .r6 8] ++ ([.subi .r8 .r8 1] : List Instr)))
      t fun t' => (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧ t'.gpr .r6 = off B (dA + 8 * i + 8) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (if c then word t.mem B (dA + 8 * i) else word t.mem B (dO + 8 * i))) ∧ Keep wlRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j5, j6, r9, h9, (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith), selectW_arith]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l6, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (d := dA + 8 * i) (by omega_arith) (by omega_arith)
    have wo : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) :=
      jout.word (d := dO + 8 * i) (by omega_arith) (by omega_arith)
    rw [lm, wordsVal_write_top _ _ _ _ _ (by omega_arith), jeq, wordsVal_succ_top s.mem B dA i,
      wordsVal_succ_top s.mem B dO i]
    cases c
    · simp only [Bool.false_eq_true, ite_false]; rw [wo]
    · simp only [ite_true]; rw [wa]

/-- Up the words: `[dO + 8 i] := c ? 0 : [dO + 8 i]` for `i < m`. -/
theorem clrUpLoop_ok {s : State} {B : Addr} {Z dO m : Nat} (hs : Scr s B Z) {c : Bool}
    (h5 : s.gpr .r5 = off B dO) (h8 : s.gpr .r8 = BitVec.ofNat 64 m) (h12 : s.gpr .r12 = complOf c)
    (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hO : dO + 8 * m ≤ Z) :
    WP isa (countLoop .r8 [.load .d .r0 .r5 0, .logic .and .r0 .r0 .r12, .store .d .r0 .r5 0, .addi .r5 .r5 8]) s
      fun t => wordsVal t.mem B dO m = (if c then 0 else wordsVal s.mem B dO m) ∧
        Outside B dO (8 * m) s.mem t.mem ∧ Keep wlRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i = (if c then 0 else wordsVal s.mem B dO i) ∧ Keep wlRegs s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, Outside.refl _ _ _ _, by simp only [wordsVal]; split <;> rfl, Keep.refl _ _⟩ h8)
    fun t ⟨_, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have r12 : t.gpr .r12 = s.gpr .r12 := jk.gpr _ (by decide)
  have hst : WP isa (.block ([.load .d .r0 .r5 0, .logic .and .r0 .r0 .r12, .store .d .r0 .r5 0, .addi .r5 .r5 8] ++
      ([.subi .r8 .r8 1] : List Instr))) t fun t' => (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) (if c then 0#64 else word t.mem B (dO + 8 * i))) ∧
      Keep wlRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j5, r12, h12, (hs.congr jk.wr).ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith), and_compl]
  refine WP.mono hst fun t' ⟨⟨l5, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wo : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) :=
      jout.word (d := dO + 8 * i) (by omega_arith) (by omega_arith)
    rw [lm, wordsVal_write_top _ _ _ _ _ (by omega_arith), jeq, wordsVal_succ_top s.mem B dO i]
    cases c
    · simp only [Bool.false_eq_true, ite_false]; rw [wo]
    · simp only [ite_true]; rfl

theorem shl3_val (n : Nat) : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem ofNat_sub' {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem off_sub (B : Addr) {d k : Nat} (hk : k ≤ d) : off B d - BitVec.ofNat 64 k = off B (d - k) :=
  BitVec.sub_eq_iff_eq_add.mpr (by rw [off_add, Nat.sub_add_cancel hk])

/-- Down the words: `[dO + 8 i] := c ? [dA + 8 i] : [dO + 8 i]` for `i < m`, from the top,
`dA` behind `dO`. -/
theorem selDownLoop_ok {s : State} {B : Addr} {Z dO dA m : Nat} (hs : Scr s B Z) {c : Bool}
    (h5 : s.gpr .r5 = off B (dO + 8 * m - 8)) (h6 : s.gpr .r6 = off B (dA + 8 * m - 8))
    (h8 : s.gpr .r8 = BitVec.ofNat 64 m) (h9 : s.gpr .r9 = maskOf c) (hm : 1 ≤ m) (hm' : m < 2 ^ 32)
    (hO : dO + 8 * m ≤ Z) (hA8 : 8 ≤ dA) (behind : dA ≤ dO) :
    WP isa (countLoop .r8 [.load .d .r0 .r5 0, .load .d .r3 .r6 0, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
      .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0, .subi .r5 .r5 8, .subi .r6 .r6 8]) s fun t =>
      wordsVal t.mem B dO m = (if c then wordsVal s.mem B dA m else wordsVal s.mem B dO m) ∧
      Outside B dO (8 * m) s.mem t.mem ∧ Keep wlRegs s t ∧ t.gpr .r5 = off B (dO - 8) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * (m - i) - 8) ∧ t.gpr .r6 = off B (dA + 8 * (m - i) - 8) ∧
      Outside B (dO + 8 * (m - i)) (8 * i) s.mem t.mem ∧
      wordsVal t.mem B (dO + 8 * (m - i)) i =
        (if c then wordsVal s.mem B (dA + 8 * (m - i)) i else wordsVal s.mem B (dO + 8 * (m - i)) i) ∧
      Keep wlRegs s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5, Nat.sub_zero], by rw [h6, Nat.sub_zero], Outside.refl _ _ _ _,
      by simp only [wordsVal]; split <;> rfl, Keep.refl _ _⟩ h8)
    fun t ⟨j5, _, jout, jeq, jk⟩ => ⟨by rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at jeq; exact jeq,
      by rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at jout; exact jout, jk,
      by rw [j5, Nat.sub_self, Nat.mul_zero, Nat.add_zero]⟩
  have r9 : t.gpr .r9 = s.gpr .r9 := jk.gpr _ (by decide)
  have ek : dO + 8 * (m - i) - 8 = dO + 8 * (m - 1 - i) := by omega_arith
  have ek' : dA + 8 * (m - i) - 8 = dA + 8 * (m - 1 - i) := by omega_arith
  rw [ek] at j5
  rw [ek'] at j6
  have hst : WP isa (.block ([.load .d .r0 .r5 0, .load .d .r3 .r6 0, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
      .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0, .subi .r5 .r5 8, .subi .r6 .r6 8] ++
      ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 8 * (m - 1 - i)) - BitVec.ofNat 64 8 ∧
        t'.gpr .r6 = off B (dA + 8 * (m - 1 - i)) - BitVec.ofNat 64 8 ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * (m - 1 - i)))
          (if c then word t.mem B (dA + 8 * (m - 1 - i)) else word t.mem B (dO + 8 * (m - 1 - i)))) ∧
      Keep wlRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j5, j6, r9, h9, (hs.congr jk.wr).ld (show dA + 8 * (m - 1 - i) + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dO + 8 * (m - 1 - i) + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * (m - 1 - i) + 8 ≤ Z by omega_arith), selectW_arith]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, off_sub B (by omega_arith)]; congr 1; omega_arith
  · rw [l6, off_sub B (by omega_arith)]; congr 1; omega_arith
  · rw [lm, show m - (i + 1) = m - 1 - i by omega_arith]
    exact (jout.mono (by omega_arith) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * (m - 1 - i)) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have e1 : dO + 8 * (m - (i + 1)) = dO + 8 * (m - 1 - i) := by omega_arith
    have e2 : dA + 8 * (m - (i + 1)) = dA + 8 * (m - 1 - i) := by omega_arith
    have wo : word t.mem B (dO + 8 * (m - 1 - i)) = word s.mem B (dO + 8 * (m - 1 - i)) :=
      jout.word (d := dO + 8 * (m - 1 - i)) (by omega_arith) (by omega_arith)
    have wa : word t.mem B (dA + 8 * (m - 1 - i)) = word s.mem B (dA + 8 * (m - 1 - i)) :=
      jout.word (d := dA + 8 * (m - 1 - i)) (by omega_arith) (by omega_arith)
    have hi8 : ∀ d, d + 8 * (m - 1 - i) + 8 = d + 8 * (m - i) := fun d => by omega_arith
    rw [e1, e2, lm, wordsVal_succ_low, word_writeW_self, hi8,
      (writeW_outside t.mem B (d := dO + 8 * (m - 1 - i)) _ (by omega_arith)).wordsVal (by omega_arith)
        (by omega_arith), jeq, wordsVal_succ_low s.mem B (dA + 8 * (m - 1 - i)), wordsVal_succ_low s.mem B
        (dO + 8 * (m - 1 - i)), hi8, hi8]
    cases c
    · simp only [Bool.false_eq_true, ite_false]; rw [wo]
    · simp only [ite_true]; rw [wa]

/-- Down the words: `[dO + 8 i] := c ? 0 : [dO + 8 i]` for `i < m`, from the top. -/
theorem clrDownLoop_ok {s : State} {B : Addr} {Z dO m : Nat} (hs : Scr s B Z) {c : Bool}
    (h5 : s.gpr .r5 = off B (dO + 8 * m - 8)) (h8 : s.gpr .r8 = BitVec.ofNat 64 m) (h12 : s.gpr .r12 = complOf c)
    (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hO : dO + 8 * m ≤ Z) (hO8 : 8 ≤ dO) :
    WP isa (countLoop .r8 [.load .d .r0 .r5 0, .logic .and .r0 .r0 .r12, .store .d .r0 .r5 0, .subi .r5 .r5 8]) s
      fun t => wordsVal t.mem B dO m = (if c then 0 else wordsVal s.mem B dO m) ∧
        Outside B dO (8 * m) s.mem t.mem ∧ Keep wlRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * (m - i) - 8) ∧ Outside B (dO + 8 * (m - i)) (8 * i) s.mem t.mem ∧
      wordsVal t.mem B (dO + 8 * (m - i)) i = (if c then 0 else wordsVal s.mem B (dO + 8 * (m - i)) i) ∧
      Keep wlRegs s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5, Nat.sub_zero], Outside.refl _ _ _ _, by simp only [wordsVal]; split <;> rfl, Keep.refl _ _⟩ h8)
    fun t ⟨_, jout, jeq, jk⟩ => ⟨by rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at jeq; exact jeq,
      by rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at jout; exact jout, jk⟩
  have r12 : t.gpr .r12 = s.gpr .r12 := jk.gpr _ (by decide)
  have ek : dO + 8 * (m - i) - 8 = dO + 8 * (m - 1 - i) := by omega_arith
  rw [ek] at j5
  have hst : WP isa (.block ([.load .d .r0 .r5 0, .logic .and .r0 .r0 .r12, .store .d .r0 .r5 0, .subi .r5 .r5 8] ++
      ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 8 * (m - 1 - i)) - BitVec.ofNat 64 8 ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * (m - 1 - i)))
          (if c then 0#64 else word t.mem B (dO + 8 * (m - 1 - i)))) ∧ Keep wlRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j5, r12, h12, (hs.congr jk.wr).ld (show dO + 8 * (m - 1 - i) + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * (m - 1 - i) + 8 ≤ Z by omega_arith), and_compl]
  refine WP.mono hst fun t' ⟨⟨l5, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, off_sub B (by omega_arith)]; congr 1; omega_arith
  · rw [lm, show m - (i + 1) = m - 1 - i by omega_arith]
    exact (jout.mono (by omega_arith) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * (m - 1 - i)) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have e1 : dO + 8 * (m - (i + 1)) = dO + 8 * (m - 1 - i) := by omega_arith
    have wo : word t.mem B (dO + 8 * (m - 1 - i)) = word s.mem B (dO + 8 * (m - 1 - i)) :=
      jout.word (d := dO + 8 * (m - 1 - i)) (by omega_arith) (by omega_arith)
    have hi8 : dO + 8 * (m - 1 - i) + 8 = dO + 8 * (m - i) := by omega_arith
    rw [e1, lm, wordsVal_succ_low, word_writeW_self, hi8,
      (writeW_outside t.mem B (d := dO + 8 * (m - 1 - i)) _ (by omega_arith)).wordsVal (by omega_arith)
        (by omega_arith), jeq, wordsVal_succ_low s.mem B (dO + 8 * (m - 1 - i)), hi8]
    cases c
    · simp only [Bool.false_eq_true, ite_false]; rw [wo]
    · simp only [ite_true]; rfl

/-! ## Shifts by whole words -/

open VG.Proof.Rsa.KeyWorkspace (arr S)

/-- `X / 2^(64 s)` is the words above the low `s`. -/
theorem wordsVal_div {m : Mem} {B : Addr} {d L sh : Nat} (hs : sh ≤ L) :
    wordsVal m B d L / 2 ^ (64 * sh) = wordsVal m B (d + 8 * sh) (L - sh) := by
  conv => lhs; rw [show L = sh + (L - sh) by omega, wordsVal_append]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wordsVal_lt _ _ _ _), Nat.zero_add]

/-- `X 2^(64 s) mod 2^(64 L)` is the low `L - s` words, up `s` words. -/
theorem wordsVal_mul_mod {m : Mem} {B : Addr} {d L sh : Nat} (hs : sh ≤ L) :
    wordsVal m B d L * 2 ^ (64 * sh) % 2 ^ (64 * L) = 2 ^ (64 * sh) * wordsVal m B d (L - sh) := by
  conv => lhs; rw [show L = (L - sh) + sh by omega, wordsVal_append]
  have hlo := wordsVal_lt m B d (L - sh)
  have e : 2 ^ (64 * (L - sh + sh)) = 2 ^ (64 * (L - sh)) * 2 ^ (64 * sh) := by rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (wordsVal m B (d + 8 * (L - sh)) sh), ← Nat.mul_assoc, ← e,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt, Nat.mul_comm]
  rw [e]; exact Nat.mul_lt_mul_of_pos_right hlo (Nat.two_pow_pos _)

/-- `shrWords j`, for `w = 2 L` and `1 ≤ s < L` (`r11`): `[j]`'s `L` words := `X / 2^(64 s)`
where the mask is set. -/
theorem shrWords_ok {s : State} {B : Addr} {Z w N j L sh : Nat} {c : Bool} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hwL : w = 2 * L) (h1 : 1 ≤ sh) (hsL : sh < L) (h11 : s.gpr .r11 = BitVec.ofNat 64 sh)
    (h9 : s.gpr .r9 = maskOf c) (h12 : s.gpr .r12 = complOf c) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shrWords j) s fun t =>
      wordsVal t.mem B (arr w j) L =
        (if c then wordsVal s.mem B (arr w j) L / 2 ^ (64 * sh) else wordsVal s.mem B (arr w j) L) ∧
      Outside B (arr w j) (8 * L) s.mem t.mem ∧ Ws t B Z w N ∧ Keep (.r7 :: wlRegs) s t := by
  have := h.wle
  have hnw := h.nowrap
  have fj := h.arr_fit hj
  simp only [S] at fj
  have e7 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 L := by rw [hwL]; exact mont_ofNat_shr1 (by omega_arith)
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.shrWords
  simp only [seqs]
  have hb1 : WP isa (.block (ptr .r5 j ++ VG.Impl.Rsa.PPC64LE.RecoverDet.lenW ++
      [.lsl .r0 .r11 3, .add .r6 .r5 .r0, .sub .r8 .r7 .r11])) s fun u =>
      (u.gpr .r5 = off B (arr w j) ∧ u.gpr .r6 = off B (arr w j + 8 * sh) ∧ u.gpr .r8 = BitVec.ofNat 64 (L - sh) ∧
        u.gpr .r7 = BitVec.ofNat 64 L ∧ u.mem = s.mem) ∧ Keep [.r0, .r5, .r6, .r7, .r8] s u := by
    rw [List.append_assoc]
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
    refine WP.mono (WP.keep [.r0, .r6, .r7, .r8] (Q := fun u => u.gpr .r6 = off B (arr w j + 8 * sh) ∧
      u.gpr .r8 = BitVec.ofNat 64 (L - sh) ∧ u.gpr .r7 = BitVec.ofNat 64 L ∧ u.mem = s.mem) (by
      prun [VG.Impl.Rsa.PPC64LE.RecoverDet.lenW, gpr_write, mem_write, h.r29, e7, h11, shl3_val, off_add,
        ofNat_sub' (show sh ≤ L by omega_arith) (show L < 2 ^ 64 by omega_arith)]) (by decide))
      fun u ⟨⟨u6, u8, u7, um⟩, uk⟩ => ⟨⟨by rw [uk.gpr .r5 (by decide)]; simp [gpr_write], u6, u8, u7,
        by rw [um]⟩, ((Keep.write _ .r5 _).trans uk).mono (by decide)⟩
  refine WP.seq (WP.mono hb1 fun s1 ⟨⟨r5, r6, r8, r7, m1⟩, k1⟩ => ?_)
  have hs1 := h.of_keep k1
  refine WP.seq (WP.mono (selUpLoop_ok (c := c) (dO := arr w j) (dA := arr w j + 8 * sh) (m := L - sh) hs1.scr
    r5 r6 r8 (by rw [k1.gpr .r9 (by decide)]; exact h9) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s2 ⟨v2, o2, k2, r52⟩ => ?_)
  have hs2 := hs1.of_keep k2
  have hb3 : WP isa (.block [.addi .r8 .r11 0]) s2 fun u => (u.gpr .r8 = BitVec.ofNat 64 sh ∧ u.mem = s2.mem) ∧
      Keep [.r8] s2 u := by
    refine WP.keep _ ?_ (by decide)
    prun [(k1.trans k2).gpr .r11 (by decide), h11, BitVec.add_zero]
  refine WP.seq (WP.mono hb3 fun s3 ⟨⟨r83, m3⟩, k3⟩ => ?_)
  have hs3 := hs2.of_keep k3
  refine WP.mono (clrUpLoop_ok (c := c) (dO := arr w j + 8 * (L - sh)) (m := sh) hs3.scr
    (by rw [k3.gpr .r5 (by decide)]; exact r52) r83 (by rw [((k1.trans k2).trans k3).gpr .r12 (by decide)]; exact h12)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨v4, o4, k4⟩ => ⟨?_, ?_, hs3.of_keep k4, ?_⟩
  · -- The low `L - s` words, and the top `s`.
    have split : ∀ mm : Mem, wordsVal mm B (arr w j) L =
        wordsVal mm B (arr w j) (L - sh) + 2 ^ (64 * (L - sh)) * wordsVal mm B (arr w j + 8 * (L - sh)) sh :=
      fun mm => by conv => lhs; rw [show L = (L - sh) + sh by omega_arith]
                   rw [wordsVal_append]
    have ehi : wordsVal s2.mem B (arr w j + 8 * (L - sh)) sh = wordsVal s.mem B (arr w j + 8 * (L - sh)) sh := by
      rw [o2.wordsVal (by omega_arith) (by omega_arith), m1]
    rw [split t.mem, v4, m3, o4.wordsVal (d := arr w j) (k := L - sh) (by omega_arith) (by omega_arith), m3, v2, m1,
      ehi]
    cases c
    · simp only [Bool.false_eq_true, ite_false]; rw [split s.mem]
    · simp only [ite_true, Nat.mul_zero, Nat.add_zero]
      rw [wordsVal_div (by omega_arith)]
  · rw [← m1]
    exact (o2.mono (by omega_arith) (by omega_arith)).trans
      (by rw [← m3]; exact o4.mono (by omega_arith) (by omega_arith))
  · exact ((((k1.trans k2).trans k3).trans k4)).mono (by decide)

/-- `shlWords j`, for `w = 2 L` and `1 ≤ s < L` (`r11`): `[j]`'s `L` words :=
`X 2^(64 s) mod 2^(64 L)` where the mask is set. -/
theorem shlWords_ok {s : State} {B : Addr} {Z w N j L sh : Nat} {c : Bool} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hwL : w = 2 * L) (h1 : 1 ≤ sh) (hsL : sh < L) (h11 : s.gpr .r11 = BitVec.ofNat 64 sh)
    (h9 : s.gpr .r9 = maskOf c) (h12 : s.gpr .r12 = complOf c) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shlWords j) s fun t =>
      wordsVal t.mem B (arr w j) L =
        (if c then wordsVal s.mem B (arr w j) L * 2 ^ (64 * sh) % 2 ^ (64 * L) else wordsVal s.mem B (arr w j) L) ∧
      Outside B (arr w j) (8 * L) s.mem t.mem ∧ Ws t B Z w N ∧ Keep (.r7 :: wlRegs) s t := by
  have := h.wle
  have hnw := h.nowrap
  have fj := h.arr_fit hj
  simp only [S] at fj
  have a8 : 8 ≤ arr w j := Nat.le_trans (by decide) (Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (j * S w))
  have e7 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 L := by rw [hwL]; exact mont_ofNat_shr1 (by omega_arith)
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.shlWords
  simp only [seqs]
  have hb1 : WP isa (.block (ptr .r5 j ++ VG.Impl.Rsa.PPC64LE.RecoverDet.lenW ++
      [.lsl .r0 .r7 3, .add .r5 .r5 .r0, .subi .r5 .r5 8, .lsl .r0 .r11 3, .sub .r6 .r5 .r0, .sub .r8 .r7 .r11])) s
      fun u => (u.gpr .r5 = off B (arr w j + 8 * sh + 8 * (L - sh) - 8) ∧
        u.gpr .r6 = off B (arr w j + 8 * (L - sh) - 8) ∧ u.gpr .r8 = BitVec.ofNat 64 (L - sh) ∧
        u.gpr .r7 = BitVec.ofNat 64 L ∧ u.mem = s.mem) ∧ Keep [.r0, .r5, .r6, .r7, .r8] s u := by
    rw [List.append_assoc]
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
    have e5 : off B (arr w j) + BitVec.ofNat 64 (8 * L) - BitVec.ofNat 64 8 =
        off B (arr w j + 8 * sh + 8 * (L - sh) - 8) := by
      rw [off_add, off_sub B (by omega_arith)]; congr 1; omega_arith
    have e6 : off B (arr w j + 8 * sh + 8 * (L - sh) - 8) - BitVec.ofNat 64 (8 * sh) =
        off B (arr w j + 8 * (L - sh) - 8) := by
      rw [off_sub B (by omega_arith)]; congr 1; omega_arith
    refine WP.mono (WP.keep [.r0, .r5, .r6, .r7, .r8] (Q := fun u =>
      u.gpr .r5 = off B (arr w j + 8 * sh + 8 * (L - sh) - 8) ∧ u.gpr .r6 = off B (arr w j + 8 * (L - sh) - 8) ∧
      u.gpr .r8 = BitVec.ofNat 64 (L - sh) ∧ u.gpr .r7 = BitVec.ofNat 64 L ∧ u.mem = s.mem) (by
      prun [VG.Impl.Rsa.PPC64LE.RecoverDet.lenW, gpr_write, mem_write, h.r29, e7, h11, shl3_val, e5, e6,
        ofNat_sub' (show sh ≤ L by omega_arith) (show L < 2 ^ 64 by omega_arith)]
      have f5 : off B (arr w j + 8 * L) - 8#64 = off B (arr w j + 8 * sh + 8 * (L - sh) - 8) := by
        rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_sub B (by omega_arith)]; congr 1; omega_arith
      rw [f5, e6]; exact ⟨rfl, rfl⟩) (by decide))
      fun u ⟨q, uk⟩ => ⟨q, ((Keep.write _ .r5 _).trans uk).mono (by decide)⟩
  refine WP.seq (WP.mono hb1 fun s1 ⟨⟨r5, r6, r8, r7, m1⟩, k1⟩ => ?_)
  have hs1 := h.of_keep k1
  refine WP.seq (WP.mono (selDownLoop_ok (c := c) (dO := arr w j + 8 * sh) (dA := arr w j) (m := L - sh) hs1.scr
    r5 r6 r8 (by rw [k1.gpr .r9 (by decide)]; exact h9) (by omega_arith) (by omega_arith) (by omega_arith)
    a8 (by omega_arith)) fun s2 ⟨v2, o2, k2, r52⟩ => ?_)
  have hs2 := hs1.of_keep k2
  have hb3 : WP isa (.block [.addi .r8 .r11 0]) s2 fun u => (u.gpr .r8 = BitVec.ofNat 64 sh ∧ u.mem = s2.mem) ∧
      Keep [.r8] s2 u := by
    refine WP.keep _ ?_ (by decide)
    prun [(k1.trans k2).gpr .r11 (by decide), h11, BitVec.add_zero]
  refine WP.seq (WP.mono hb3 fun s3 ⟨⟨r83, m3⟩, k3⟩ => ?_)
  have hs3 := hs2.of_keep k3
  refine WP.mono (clrDownLoop_ok (c := c) (dO := arr w j) (m := sh) hs3.scr
    (by rw [k3.gpr .r5 (by decide), r52]) r83 (by rw [((k1.trans k2).trans k3).gpr .r12 (by decide)]; exact h12)
    (by omega_arith) (by omega_arith) (by omega_arith) a8) fun t ⟨v4, o4, k4⟩ => ⟨?_, ?_, hs3.of_keep k4, ?_⟩
  · -- The low `s` words, and the top `L - s`.
    have split : ∀ mm : Mem, wordsVal mm B (arr w j) L =
        wordsVal mm B (arr w j) sh + 2 ^ (64 * sh) * wordsVal mm B (arr w j + 8 * sh) (L - sh) :=
      fun mm => by conv => lhs; rw [show L = sh + (L - sh) by omega_arith]
                   rw [wordsVal_append]
    have elo : wordsVal s2.mem B (arr w j) sh = wordsVal s.mem B (arr w j) sh := by
      rw [o2.wordsVal (by omega_arith) (by omega_arith), m1]
    rw [split t.mem, v4, m3, o4.wordsVal (d := arr w j + 8 * sh) (k := L - sh) (by omega_arith) (by omega_arith),
      m3, v2, m1, elo]
    cases c
    · simp only [Bool.false_eq_true, ite_false]; rw [split s.mem]
    · simp only [ite_true, Nat.zero_add]
      rw [wordsVal_mul_mod (by omega_arith)]
  · rw [← m1]
    exact (o2.mono (by omega_arith) (by omega_arith)).trans
      (by rw [← m3]; exact o4.mono (by omega_arith) (by omega_arith))
  · exact ((((k1.trans k2).trans k3).trans k4)).mono (by decide)

/-! ## Shifts by bits -/

/-- The shift right's loop: words `i < m` := `c ? (x_i >> b) + (x_{i+1} << (64 - b)) : x_i`,
up the words from `d`, reading the next word before it changes. -/
theorem shrBitsLoop_ok {s : State} {B : Addr} {Z d m b : Nat} (hs : Scr s B Z) {c : Bool}
    (hb : 0 < b) (hb' : b < 64)
    (h5 : s.gpr .r5 = off B d) (h8 : s.gpr .r8 = BitVec.ofNat 64 m) (h9 : s.gpr .r9 = maskOf c)
    (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hZ : d + 8 * (m + 1) ≤ Z) :
    WP isa (countLoop .r8 [.load .d .r0 .r5 0, .load .d .r3 .r5 8, .lsl .r3 .r3 (64 - b), .lsr .d .r6 .r0 b,
      .add .r3 .r6 .r3, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9, .logic .xor .r3 .r3 .r0,
      .store .d .r3 .r5 0, .addi .r5 .r5 8]) s fun t =>
      (if c then wordsVal t.mem B d m + 2 ^ (64 * m) * ((word s.mem B (d + 8 * m)).toNat / 2 ^ b) =
          wordsVal s.mem B d (m + 1) / 2 ^ b
        else wordsVal t.mem B d m = wordsVal s.mem B d m) ∧
      Outside B d (8 * m) s.mem t.mem ∧ Keep wlRegs s t ∧ t.gpr .r5 = off B (d + 8 * m) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (d + 8 * i) ∧ Outside B d (8 * i) s.mem t.mem ∧
      (if c then wordsVal t.mem B d i + 2 ^ (64 * i) * ((word s.mem B (d + 8 * i)).toNat / 2 ^ b) =
          wordsVal s.mem B d (i + 1) / 2 ^ b
        else wordsVal t.mem B d i = wordsVal s.mem B d i) ∧ Keep wlRegs s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, Outside.refl _ _ _ _, by
      cases c
      · rfl
      · simp only [ite_true, wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.zero_add],
      Keep.refl _ _⟩ h8)
    fun t ⟨j5, jout, jeq, jk⟩ => ⟨jeq, jout, jk, j5⟩
  have r9 : t.gpr .r9 = s.gpr .r9 := jk.gpr _ (by decide)
  have hst : WP isa (.block ([.load .d .r0 .r5 0, .load .d .r3 .r5 8, .lsl .r3 .r3 (64 - b), .lsr .d .r6 .r0 b,
      .add .r3 .r6 .r3, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9, .logic .xor .r3 .r3 .r0,
      .store .d .r3 .r5 0, .addi .r5 .r5 8] ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (d + 8 * i + 8) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (d + 8 * i))
          (if c then word t.mem B (d + 8 * i) >>> b + word t.mem B (d + 8 * i + 8) <<< (64 - b)
            else word t.mem B (d + 8 * i))) ∧ Keep wlRegs t t' := by
    refine WP.keep _ ?_ (by rfl)
    prun [j5, r9, h9, exec_lsr_d hb', exec_lsl (show 64 - b < 64 by omega_arith), off_add,
      (hs.congr jk.wr).ld (show d + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show d + 8 * i + 8 + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show d + 8 * i + 8 ≤ Z by omega_arith), selectW_arith]
  refine WP.mono hst fun t' ⟨⟨l5, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := d + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wx : word t.mem B (d + 8 * i) = word s.mem B (d + 8 * i) :=
      jout.word (d := d + 8 * i) (by omega_arith) (by omega_arith)
    have wy : word t.mem B (d + 8 * i + 8) = word s.mem B (d + 8 * (i + 1)) := by
      rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith]
      exact jout.word (d := d + 8 * (i + 1)) (by omega_arith) (by omega_arith)
    rw [lm, wordsVal_write_top _ _ _ _ _ (by omega_arith)]
    cases c
    · simp only [Bool.false_eq_true, ite_false] at jeq ⊢
      rw [jeq, wx, wordsVal_succ_top s.mem B d i]
    · simp only [ite_true] at jeq ⊢
      rw [wx, wy, funnel_val _ _ hb hb', wordsVal_succ_top s.mem B d (i + 1)]
      exact shrB_step (by omega_arith) jeq

/-- `shrBits j b`, for `w = 2 L`, `L ≥ 2`, `0 < b < 64`: `[j]`'s `L` words := `X / 2^b` where
the mask is set. -/
theorem shrBits_ok {s : State} {B : Addr} {Z w N j L b : Nat} {c : Bool} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hwL : w = 2 * L) (hL : 2 ≤ L) (hb : 0 < b) (hb' : b < 64) (h9 : s.gpr .r9 = maskOf c) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shrBits j b) s fun t =>
      wordsVal t.mem B (arr w j) L =
        (if c then wordsVal s.mem B (arr w j) L / 2 ^ b else wordsVal s.mem B (arr w j) L) ∧
      Outside B (arr w j) (8 * L) s.mem t.mem ∧ Ws t B Z w N ∧ Keep (.r7 :: wlRegs) s t := by
  have := h.wle
  have hnw := h.nowrap
  have fj := h.arr_fit hj
  simp only [S] at fj
  have e7 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 L := by rw [hwL]; exact mont_ofNat_shr1 (by omega_arith)
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.shrBits
  simp only [seqs]
  have hb1 : WP isa (.block (ptr .r5 j ++ VG.Impl.Rsa.PPC64LE.RecoverDet.lenW ++ [.subi .r8 .r7 1])) s fun u =>
      (u.gpr .r5 = off B (arr w j) ∧ u.gpr .r8 = BitVec.ofNat 64 (L - 1) ∧ u.gpr .r7 = BitVec.ofNat 64 L ∧
        u.mem = s.mem) ∧ Keep [.r5, .r7, .r8] s u := by
    rw [List.append_assoc]
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
    refine WP.mono (WP.keep [.r7, .r8] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 (L - 1) ∧
      u.gpr .r7 = BitVec.ofNat 64 L ∧ u.mem = s.mem) (by
      prun [VG.Impl.Rsa.PPC64LE.RecoverDet.lenW, gpr_write, mem_write, h.r29, e7,
        ofNat_sub' (show 1 ≤ L by omega_arith) (show L < 2 ^ 64 by omega_arith)]) (by decide))
      fun u ⟨⟨u8, u7, um⟩, uk⟩ => ⟨⟨by rw [uk.gpr .r5 (by decide)]; simp [gpr_write], u8, u7, by rw [um]⟩,
        ((Keep.write _ .r5 _).trans uk).mono (by decide)⟩
  refine WP.seq (WP.mono hb1 fun s1 ⟨⟨r5, r8, r7, m1⟩, k1⟩ => ?_)
  have hs1 := h.of_keep k1
  refine WP.seq (WP.mono (shrBitsLoop_ok (c := c) (d := arr w j) (m := L - 1) hs1.scr hb hb' r5 r8
    (by rw [k1.gpr .r9 (by decide)]; exact h9) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s2 ⟨v2, o2, k2, r52⟩ => ?_)
  have hs2 := hs1.of_keep k2
  have hb3 : WP isa (.block [.load .d .r0 .r5 0, .lsr .d .r3 .r0 b, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
      .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0]) s2 fun u =>
      (u.mem = s2.mem.writeW (off B (arr w j + 8 * (L - 1)))
        (if c then word s2.mem B (arr w j + 8 * (L - 1)) >>> b else word s2.mem B (arr w j + 8 * (L - 1)))) ∧
      Keep [.r0, .r3] s2 u := by
    refine WP.keep _ ?_ (by rfl)
    prun [r52, (k1.trans k2).gpr .r9 (by decide), h9, exec_lsr_d hb',
      hs2.scr.ld (show arr w j + 8 * (L - 1) + 8 ≤ Z by omega_arith),
      hs2.scr.st (show arr w j + 8 * (L - 1) + 8 ≤ Z by omega_arith), selectW_arith]
  refine WP.mono hb3 fun t ⟨tm, k3⟩ => ⟨?_, ?_, hs2.of_keep k3, ((k1.trans k2).trans k3).mono (by decide)⟩
  · have wt : word s2.mem B (arr w j + 8 * (L - 1)) = word s.mem B (arr w j + 8 * (L - 1)) := by
      rw [o2.word (d := arr w j + 8 * (L - 1)) (by omega_arith) (by omega_arith), m1]
    have eL : ∀ mm : Mem, wordsVal mm B (arr w j) L = wordsVal mm B (arr w j) (L - 1 + 1) := fun mm => by
      rw [Nat.sub_add_cancel (by omega_arith)]
    rw [m1] at v2
    rw [eL t.mem, eL s.mem, tm, wordsVal_write_top _ _ _ _ _ (by omega_arith), wt]
    cases c
    · simp only [Bool.false_eq_true, ite_false] at v2 ⊢
      rw [v2, wordsVal_succ_top s.mem B (arr w j) (L - 1)]
    · simp only [ite_true] at v2 ⊢
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact v2
  · rw [← m1, tm]
    exact (o2.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := arr w j + 8 * (L - 1)) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- A word shifted left by `b`. -/
theorem shl_val (x : BitVec 64) {b : Nat} (hb : 0 < b) (hb' : b < 64) :
    (x <<< b).toNat = 2 ^ b * (x.toNat % 2 ^ (64 - b)) := by
  have := funnel_val 0#64 x (c := 64 - b) (by omega) (by omega)
  rw [show 64 - (64 - b) = b by omega, BitVec.zero_ushiftRight, BitVec.zero_add] at this
  rw [this]; simp

/-- The shift left's loop: down the words from `d + 8 (m - 1)`, word `j` (for `1 ≤ j ≤ m`, `d` word
`0`) := `c ? (x_{j-1} >> (64 - b)) + (x_j << b) : x_j`, reading the word below before it changes. -/
theorem shlBitsLoop_ok {s : State} {B : Addr} {Z d m b : Nat} (hs : Scr s B Z) {c : Bool}
    (hb : 0 < b) (hb' : b < 64)
    (h5 : s.gpr .r5 = off B (d + 8 * m)) (h6 : s.gpr .r6 = off B (d + 8 * m - 8))
    (h8 : s.gpr .r8 = BitVec.ofNat 64 m) (h9 : s.gpr .r9 = maskOf c)
    (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hZ : d + 8 * (m + 1) ≤ Z) (hd : 8 ≤ d) :
    WP isa (countLoop .r8 [.load .d .r0 .r5 0, .load .d .r3 .r6 0, .lsr .d .r3 .r3 (64 - b), .lsl .r10 .r0 b,
      .add .r3 .r3 .r10, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9, .logic .xor .r3 .r3 .r0,
      .store .d .r3 .r5 0, .subi .r5 .r5 8, .subi .r6 .r6 8]) s fun t =>
      (if c then wordsVal t.mem B (d + 8) m =
          (wordsVal s.mem B (d + 8) m * 2 ^ b + (word s.mem B d).toNat / 2 ^ (64 - b)) % 2 ^ (64 * m)
        else wordsVal t.mem B (d + 8) m = wordsVal s.mem B (d + 8) m) ∧
      Outside B (d + 8) (8 * m) s.mem t.mem ∧ Keep (.r10 :: wlRegs) s t ∧ t.gpr .r5 = off B d := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun k t =>
    t.gpr .r5 = off B (d + 8 * (m - k)) ∧ t.gpr .r6 = off B (d + 8 * (m - k) - 8) ∧
      Outside B (d + 8 * (m - k) + 8) (8 * k) s.mem t.mem ∧
      (if c then wordsVal t.mem B (d + 8 * (m - k) + 8) k =
          (wordsVal s.mem B (d + 8 * (m - k) + 8) k * 2 ^ b + (word s.mem B (d + 8 * (m - k))).toNat / 2 ^ (64 - b)) %
            2 ^ (64 * k)
        else wordsVal t.mem B (d + 8 * (m - k) + 8) k = wordsVal s.mem B (d + 8 * (m - k) + 8) k) ∧
      Keep (.r10 :: wlRegs) s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun k hk t ⟨j5, j6, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5, Nat.sub_zero], by rw [h6, Nat.sub_zero], Outside.refl _ _ _ _, by
      cases c
      · rfl
      · simp only [ite_true, wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.mod_one], Keep.refl _ _⟩ h8)
    fun t ⟨j5, _, jout, jeq, jk⟩ => ⟨by simpa only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] using jeq,
      by simpa only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] using jout, jk,
      by simpa only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] using j5⟩
  have r9 : t.gpr .r9 = s.gpr .r9 := jk.gpr _ (by decide)
  -- Word `j = m - k` from `x_j` and `x_{j-1}`.
  have ej : d + 8 * (m - k) - 8 = d + 8 * (m - k - 1) := by omega_arith
  rw [ej] at j6
  have hst : WP isa (.block ([.load .d .r0 .r5 0, .load .d .r3 .r6 0, .lsr .d .r3 .r3 (64 - b), .lsl .r10 .r0 b,
      .add .r3 .r3 .r10, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9, .logic .xor .r3 .r3 .r0,
      .store .d .r3 .r5 0, .subi .r5 .r5 8, .subi .r6 .r6 8] ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (d + 8 * (m - k)) - BitVec.ofNat 64 8 ∧
        t'.gpr .r6 = off B (d + 8 * (m - k - 1)) - BitVec.ofNat 64 8 ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (d + 8 * (m - k)))
          (if c then word t.mem B (d + 8 * (m - k - 1)) >>> (64 - b) + word t.mem B (d + 8 * (m - k)) <<< b
            else word t.mem B (d + 8 * (m - k)))) ∧ Keep (.r10 :: wlRegs) t t' := by
    refine WP.keep _ ?_ (by rfl)
    prun [j5, j6, r9, h9, exec_lsr_d (show 64 - b < 64 by omega_arith), exec_lsl hb',
      (hs.congr jk.wr).ld (show d + 8 * (m - k) + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show d + 8 * (m - k - 1) + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show d + 8 * (m - k) + 8 ≤ Z by omega_arith), selectW_arith]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, off_sub B (by omega_arith)]; congr 1
  · rw [l6, off_sub B (by omega_arith)]; congr 1
  · rw [lm, show d + 8 * (m - (k + 1)) + 8 = d + 8 * (m - k) by omega_arith]
    exact (jout.mono (by omega_arith) (by omega_arith)).trans
      ((writeW_outside _ B (d := d + 8 * (m - k)) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have e1 : d + 8 * (m - (k + 1)) + 8 = d + 8 * (m - k) := by omega_arith
    have e2 : d + 8 * (m - (k + 1)) = d + 8 * (m - k - 1) := by omega_arith
    have wz : word t.mem B (d + 8 * (m - k)) = word s.mem B (d + 8 * (m - k)) :=
      jout.word (d := d + 8 * (m - k)) (by omega_arith) (by omega_arith)
    have wy : word t.mem B (d + 8 * (m - k - 1)) = word s.mem B (d + 8 * (m - k - 1)) :=
      jout.word (d := d + 8 * (m - k - 1)) (by omega_arith) (by omega_arith)
    have hw : wordsVal (t.mem.writeW (off B (d + 8 * (m - k)))
        (if c then word t.mem B (d + 8 * (m - k - 1)) >>> (64 - b) + word t.mem B (d + 8 * (m - k)) <<< b
          else word t.mem B (d + 8 * (m - k)))) B (d + 8 * (m - k) + 8) k =
        wordsVal t.mem B (d + 8 * (m - k) + 8) k :=
      (writeW_outside t.mem B (d := d + 8 * (m - k)) _ (by omega_arith)).wordsVal (by omega_arith) (by omega_arith)
    rw [e1, e2, lm, wordsVal_succ_low, word_writeW_self, hw, wordsVal_succ_low s.mem B (d + 8 * (m - k)), wz, wy]
    cases c
    · simp only [Bool.false_eq_true, ite_false] at jeq ⊢
      rw [jeq]
    · simp only [ite_true] at jeq ⊢
      have fv := funnel_val (word s.mem B (d + 8 * (m - k - 1))) (word s.mem B (d + 8 * (m - k))) (c := 64 - b)
        (by omega_arith) (by omega_arith)
      rw [show 64 - (64 - b) = b by omega_arith] at fv
      rw [fv, jeq]
      exact shlB_step hb hb' (word s.mem B (d + 8 * (m - k - 1))).isLt rfl

/-- `shlBits j b`, for `w = 2 L`, `L ≥ 2`, `0 < b < 64`: `[j]`'s `L` words := `X 2^b mod 2^(64 L)`
where the mask is set. -/
theorem shlBits_ok {s : State} {B : Addr} {Z w N j L b : Nat} {c : Bool} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hwL : w = 2 * L) (hL : 2 ≤ L) (hb : 0 < b) (hb' : b < 64) (h9 : s.gpr .r9 = maskOf c) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shlBits j b) s fun t =>
      wordsVal t.mem B (arr w j) L =
        (if c then wordsVal s.mem B (arr w j) L * 2 ^ b % 2 ^ (64 * L) else wordsVal s.mem B (arr w j) L) ∧
      Outside B (arr w j) (8 * L) s.mem t.mem ∧ Ws t B Z w N ∧ Keep (.r7 :: .r10 :: wlRegs) s t := by
  have := h.wle
  have hnw := h.nowrap
  have fj := h.arr_fit hj
  simp only [S] at fj
  have a8 : 8 ≤ arr w j := Nat.le_trans (by decide) (Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (j * S w))
  have e7 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 L := by rw [hwL]; exact mont_ofNat_shr1 (by omega_arith)
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.shlBits
  simp only [seqs]
  have hb1 : WP isa (.block (ptr .r5 j ++ VG.Impl.Rsa.PPC64LE.RecoverDet.lenW ++
      [.lsl .r0 .r7 3, .add .r5 .r5 .r0, .subi .r5 .r5 8, .subi .r6 .r5 8, .subi .r8 .r7 1])) s fun u =>
      (u.gpr .r5 = off B (arr w j + 8 * (L - 1)) ∧ u.gpr .r6 = off B (arr w j + 8 * (L - 1) - 8) ∧
        u.gpr .r8 = BitVec.ofNat 64 (L - 1) ∧ u.gpr .r7 = BitVec.ofNat 64 L ∧ u.mem = s.mem) ∧
      Keep [.r0, .r5, .r6, .r7, .r8] s u := by
    rw [List.append_assoc]
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
    refine WP.mono (WP.keep [.r0, .r5, .r6, .r7, .r8] (Q := fun u => u.gpr .r5 = off B (arr w j + 8 * (L - 1)) ∧
      u.gpr .r6 = off B (arr w j + 8 * (L - 1) - 8) ∧ u.gpr .r8 = BitVec.ofNat 64 (L - 1) ∧
      u.gpr .r7 = BitVec.ofNat 64 L ∧ u.mem = s.mem) (by
      prun [VG.Impl.Rsa.PPC64LE.RecoverDet.lenW, gpr_write, mem_write, h.r29, e7, shl3_val, off_add,
        ofNat_sub' (show 1 ≤ L by omega_arith) (show L < 2 ^ 64 by omega_arith)]
      have f5 : off B (arr w j + 8 * L) - 8#64 = off B (arr w j + 8 * (L - 1)) := by
        rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_sub B (by omega_arith)]; congr 1; omega_arith
      have f6 : off B (arr w j + 8 * (L - 1)) - 8#64 = off B (arr w j + 8 * (L - 1) - 8) := by
        rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_sub B (by omega_arith)]
      rw [f5, f6]; exact ⟨rfl, rfl⟩) (by decide))
      fun u ⟨q, uk⟩ => ⟨q, ((Keep.write _ .r5 _).trans uk).mono (by decide)⟩
  refine WP.seq (WP.mono hb1 fun s1 ⟨⟨r5, r6, r8, r7, m1⟩, k1⟩ => ?_)
  have hs1 := h.of_keep k1
  refine WP.seq (WP.mono (shlBitsLoop_ok (c := c) (d := arr w j) (m := L - 1) hs1.scr hb hb' r5 r6 r8
    (by rw [k1.gpr .r9 (by decide)]; exact h9) (by omega_arith) (by omega_arith) (by omega_arith) a8)
    fun s2 ⟨v2, o2, k2, r52⟩ => ?_)
  have hs2 := hs1.of_keep k2
  have hb3 : WP isa (.block [.load .d .r0 .r5 0, .lsl .r3 .r0 b, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
      .logic .xor .r3 .r3 .r0, .store .d .r3 .r5 0]) s2 fun u =>
      (u.mem = s2.mem.writeW (off B (arr w j))
        (if c then word s2.mem B (arr w j) <<< b else word s2.mem B (arr w j))) ∧ Keep [.r0, .r3] s2 u := by
    refine WP.keep _ ?_ (by rfl)
    prun [r52, (k1.trans k2).gpr .r9 (by decide), h9, exec_lsl hb',
      hs2.scr.ld (show arr w j + 8 ≤ Z by omega_arith), hs2.scr.st (show arr w j + 8 ≤ Z by omega_arith),
      selectW_arith]
  refine WP.mono hb3 fun t ⟨tm, k3⟩ => ⟨?_, ?_, hs2.of_keep k3, ((k1.trans k2).trans k3).mono (by decide)⟩
  · have wt : word s2.mem B (arr w j) = word s.mem B (arr w j) := by
      rw [o2.word (d := arr w j) (by omega_arith) (by omega_arith), m1]
    rw [m1] at v2
    have eL : ∀ mm : Mem, wordsVal mm B (arr w j) L = wordsVal mm B (arr w j) (L - 1 + 1) := fun mm => by
      rw [Nat.sub_add_cancel (by omega_arith)]
    have hw : wordsVal (s2.mem.writeW (off B (arr w j))
        (if c then word s2.mem B (arr w j) <<< b else word s2.mem B (arr w j))) B (arr w j + 8) (L - 1) =
        wordsVal s2.mem B (arr w j + 8) (L - 1) :=
      (writeW_outside s2.mem B (d := arr w j) _ (by omega_arith)).wordsVal (by omega_arith) (by omega_arith)
    rw [eL t.mem, eL s.mem, tm, wordsVal_succ_low, word_writeW_self, hw, wt, wordsVal_succ_low s.mem]
    cases c
    · simp only [Bool.false_eq_true, ite_false] at v2 ⊢
      rw [v2]
    · simp only [ite_true] at v2 ⊢
      rw [shl_val _ hb hb', v2]
      have := shlB_step (y := 0) (z := (word s.mem B (arr w j)).toNat) (Q := wordsVal s.mem B (arr w j + 8) (L - 1))
        (k := L - 1) hb hb' (by decide) rfl
      rw [Nat.zero_div, Nat.zero_add, Nat.add_zero, Nat.sub_add_cancel (show 1 ≤ L by omega_arith)] at this
      exact this
  · rw [← m1, tm]
    exact (o2.mono (by omega_arith) (by omega_arith)).trans
      ((writeW_outside _ B (d := arr w j) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-! ## The masks of a count's bits -/

/-- The bit of `c &&& v` that `(x | -x) >>> 63` takes. -/
theorem and_bit {c v : Nat} (hc : c < 2 ^ 64) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 c &&& BitVec.ofNat 64 v ||| (BitVec.ofNat 64 0 - (BitVec.ofNat 64 c &&& BitVec.ofNat 64 v))) >>> 63 =
      BitVec.ofNat 64 (if decide (c &&& v ≠ 0) then 1 else 0) := by
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, nz_bit]
  have e : (BitVec.ofNat 64 c &&& BitVec.ofNat 64 v = 0#64) ↔ c &&& v = 0 := by
    constructor
    · intro h; have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hv] at this
    · intro h; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hv, h]; rfl
  by_cases h : c &&& v = 0
  · have hx := e.mpr h
    simp only [hx, ↓reduceIte, h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true]
  · have hx : ¬ (BitVec.ofNat 64 c &&& BitVec.ofNat 64 v = 0#64) := fun h' => h (e.mp h')
    simp only [hx, ↓reduceIte, h, ne_eq, not_false_eq_true, decide_true]

/-- Bit `k` of `c`, by its `and` with `2^k`. -/
theorem decide_and_pow (c k : Nat) : decide (c &&& 2 ^ k ≠ 0) = decide (c / 2 ^ k % 2 = 1) := by
  have := and_pow_eq_zero_iff c k
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h; by_contra h'; exact h (this.mpr (by omega))
  · intro h h0; have := this.mp h0; omega

open VG.Proof.Rsa.PPC64LE.Recover (ld_slot) in
/-- `wordMask sl`, `r11 = 2^k`: the mask of bit `k` of the slot `sl`, and its complement. -/
theorem wordMask_ok {s : State} {B : Addr} {Z w N sl cw k : Nat} (h : Ws s B Z w N) (hsl : sl + 4 ≤ 160)
    (hslot : slot s.mem B sl = cw) (hk : k < 64) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 ^ k)) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.RecoverDet.wordMask sl)) s fun u =>
      (u.gpr .r9 = maskOf (decide (cw / 2 ^ k % 2 = 1)) ∧ u.gpr .r12 = complOf (decide (cw / 2 ^ k % 2 = 1)) ∧
        u.mem = s.mem) ∧ Keep [.r0, .r3, .r9, .r10, .r12] s u := by
  have hz : 160 ≤ Z := h.hdr_le
  have hcw : cw < 2 ^ 64 := by rw [← hslot]; exact Nat.lt_trans (show slot s.mem B sl < 2 ^ 32 from BitVec.isLt _) (by decide)
  have hp : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  refine WP.keep _ ?_ (by rfl)
  prun [VG.Impl.Rsa.PPC64LE.RecoverDet.wordMask, h.r31, h11, ld_slot hslot,
    h.scr.ld (show sl + 4 ≤ Z by omega_arith),
    exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sl < 2 ^ 15 by omega_arith), and_bit hcw hp, decide_and_pow]

open VG.Proof.Rsa.PPC64LE.Recover (ld_slot) in
/-- `bitMask sl (2^k)`: the mask of bit `k` of the slot `sl`. -/
theorem bitMask_ok {s : State} {B : Addr} {Z w N sl cb k : Nat} (h : Ws s B Z w N) (hsl : sl + 4 ≤ 160)
    (hslot : slot s.mem B sl = cb) (hk : 2 ^ k < 2 ^ 15) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.RecoverDet.bitMask sl (2 ^ k))) s fun u =>
      (u.gpr .r9 = maskOf (decide (cb / 2 ^ k % 2 = 1)) ∧ u.mem = s.mem) ∧ Keep [.r0, .r3, .r9, .r10] s u := by
  have hz : 160 ≤ Z := h.hdr_le
  have hcb : cb < 2 ^ 64 := by rw [← hslot]; exact Nat.lt_trans (show slot s.mem B sl < 2 ^ 32 from BitVec.isLt _) (by decide)
  have hp : 2 ^ k < 2 ^ 64 := Nat.lt_trans hk (by decide)
  refine WP.keep _ ?_ (by rfl)
  prun [VG.Impl.Rsa.PPC64LE.RecoverDet.bitMask, h.r31, ld_slot hslot, exec_li hk,
    h.scr.ld (show sl + 4 ≤ Z by omega_arith),
    exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sl < 2 ^ 15 by omega_arith), and_bit hcb hp, decide_and_pow]

/-! ## The stages in turn -/

/-- The stages' test: the sign of `a - b`, for `a, b < 2^63`. -/
theorem sub_sign {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
  split <;> omega

theorem pow_shl1 {k : Nat} (hk : k < 63) : BitVec.ofNat 64 (2 ^ k) <<< 1 = BitVec.ofNat 64 (2 ^ (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ k < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) hk
  have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [h2]; omega

/-- The word stages of a shift `sh` of `[j]`'s `L` words (by `s` words, `1 ≤ s < L`, in `r11`, where the
mask is set: `G s`), by the count `c_w < L` in the slot `sl`: `[j] := F c_w` from `F 0`, for `G s (F a) = F (a + s)`. -/
theorem wordStages_ok {s : State} {B : Addr} {Z w N j L sl cw : Nat} (sh : Prog isa) (G : Nat → Nat → Nat)
    (F : Nat → Nat) (rs : List Reg) (h : Ws s B Z w N) (hwL : w = 2 * L) (hL : 2 ≤ L) (hcw : cw < L)
    (hsl : sl + 4 ≤ 160) (hslot : slot s.mem B sl = cw) (hj8 : 160 ≤ arr w j) (h11 : Reg.r11 ∉ rs)
    (hsh : ∀ (u : State) (k : Nat) (c : Bool), Ws u B Z w N → 1 ≤ k → k < L → u.gpr .r11 = BitVec.ofNat 64 k →
      u.gpr .r9 = maskOf c → u.gpr .r12 = complOf c →
      WP isa sh u fun u' => wordsVal u'.mem B (arr w j) L =
          (if c then G k (wordsVal u.mem B (arr w j) L) else wordsVal u.mem B (arr w j) L) ∧
        Outside B (arr w j) (8 * L) u.mem u'.mem ∧ Ws u' B Z w N ∧ Keep rs u u')
    (hG : ∀ a k, G k (F a) = F (a + k)) (h0 : wordsVal s.mem B (arr w j) L = F 0) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.wordStages sl sh) s fun t =>
      wordsVal t.mem B (arr w j) L = F cw ∧ Outside B (arr w j) (8 * L) s.mem t.mem ∧ Ws t B Z w N ∧
      Keep (([.r0, .r3, .r7, .r9, .r10, .r11, .r12] : List Reg) ++ rs) s t := by
  have := h.wle
  have hnw := h.nowrap
  have e7 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 L := by rw [hwL]; exact mont_ofNat_shr1 (by omega_arith)
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.wordStages
  have hb0 : WP isa (.block [.li .r11 1]) s fun u => (u.gpr .r11 = BitVec.ofNat 64 (2 ^ 0) ∧ u.mem = s.mem) ∧
      Keep [.r11] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [exec_li (show 1 < 2 ^ 15 by decide)]
  refine WP.seq (WP.mono hb0 fun s1 ⟨⟨r11, m1⟩, k1⟩ => ?_)
  let Inv : Nat → State → Prop := fun n u => ∃ jj, n = L - 2 ^ jj ∧ 2 ^ jj < L ∧
    u.gpr .r11 = BitVec.ofNat 64 (2 ^ jj) ∧ wordsVal u.mem B (arr w j) L = F (cw % 2 ^ jj) ∧
    Outside B (arr w j) (8 * L) s.mem u.mem ∧ Ws u B Z w N ∧ Keep ([.r0, .r3, .r7, .r9, .r10, .r11, .r12] ++ rs) s u
  refine WP.loop Inv (fun n u ⟨jj, hn, hlt, u11, uv, uo, uw, uk⟩ => ?_) (L - 2 ^ 0) s1
    ⟨0, rfl, by omega_arith, r11, by rw [m1, h0, Nat.pow_zero, Nat.mod_one], by rw [m1]; exact Outside.refl _ _ _ _,
      h.of_keep k1, k1.mono (by simp)⟩
  have hjj : jj < 10 := by
    by_contra hc
    have : 2 ^ 10 ≤ 2 ^ jj := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  have hp : 2 ^ jj < 2 ^ 10 := Nat.pow_lt_pow_right (by decide) hjj
  have uslot : slot u.mem B sl = cw := by
    rw [← hslot]; exact uo.w32 (by omega_arith) (by omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (wordMask_ok uw hsl uslot (by omega_arith) u11) fun u1 ⟨⟨r9, r12, m2⟩, k2⟩ => ?_)
  have uw1 := uw.of_keep k2
  refine WP.seq (WP.mono (hsh u1 (2 ^ jj) _ uw1 Nat.one_le_two_pow hlt (by rw [k2.gpr .r11 (by decide), u11]) r9 r12)
    fun u2 ⟨v2, o2, uw2, k3⟩ => ?_)
  have hb4 : WP isa (.block (VG.Impl.Rsa.PPC64LE.RecoverDet.lenW ++ [.lsl .r11 .r11 1, .sub .r0 .r11 .r7,
      .lsr .d .r0 .r0 63])) u2 fun v =>
      (v.gpr .r11 = BitVec.ofNat 64 (2 ^ (jj + 1)) ∧ v.gpr .r0 = BitVec.ofNat 64 (if 2 ^ (jj + 1) < L then 1 else 0) ∧
        v.mem = u2.mem) ∧ Keep [.r0, .r7, .r11] u2 v := by
    have r112 : u2.gpr .r11 = BitVec.ofNat 64 (2 ^ jj) := by
      rw [k3.gpr .r11 h11, k2.gpr .r11 (by decide), u11]
    refine WP.keep _ ?_ (by decide)
    prun [VG.Impl.Rsa.PPC64LE.RecoverDet.lenW, uw2.r29, e7, r112, pow_shl1 (show jj < 63 by omega_arith),
      sub_sign (show 2 ^ (jj + 1) < 2 ^ 63 by have := Nat.pow_lt_pow_right (a := 2) (by decide) (show jj + 1 < 63 by omega_arith); omega_arith)
        (show L < 2 ^ 63 by omega_arith)]
  refine WP.mono hb4 fun v ⟨⟨v11, v0, vm⟩, k4⟩ => ?_
  have hval : wordsVal v.mem B (arr w j) L = F (cw % 2 ^ (jj + 1)) := by
    rw [vm, v2, m2, uv, VG.Proof.Bignum.ShiftStages.mod_two_pow_succ]
    by_cases hb : cw / 2 ^ jj % 2 = 1
    · simp only [hb, decide_true, ite_true, hG, Nat.one_mul]
    · have : cw / 2 ^ jj % 2 = 0 := by omega_arith
      simp only [this, Nat.zero_mul, Nat.add_zero, show decide (0 = 1) = false from rfl, Bool.false_eq_true,
        ite_false]
  have hout : Outside B (arr w j) (8 * L) s.mem v.mem := by
    rw [vm]; exact uo.trans (by rw [← m2]; exact o2)
  have hkv : Keep ([.r0, .r3, .r7, .r9, .r10, .r11, .r12] ++ rs) s v :=
    (((uk.trans k2).trans k3).trans k4).mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with ((hr | hr) | hr) | hr
      · exact hr
      · rcases hr with h | h | h | h | h <;> simp [h]
      · exact .inr hr
      · rcases hr with h | h | h <;> simp [h]
  have ev := eval_nonzero_ofNat' v .r0 (by split <;> decide) v0
  by_cases hc : 2 ^ (jj + 1) < L
  · refine .inr ⟨ev.trans (by simp [hc]), L - 2 ^ (jj + 1), ?_, jj + 1, rfl, hc, v11, hval, hout, uw2.of_keep k4,
      hkv⟩
    have h1 := Nat.one_le_two_pow (n := jj)
    have h2 : 2 ^ (jj + 1) = 2 ^ jj * 2 := Nat.pow_succ ..
    rw [hn]; omega
  · refine .inl ⟨ev.trans (by simp [hc]), ?_, hout, uw2.of_keep k4, hkv⟩
    rw [hval, Nat.mod_eq_of_lt (by omega_arith)]

/-- The bits of `c` that stages of `bs` take: `b` where bit `log₂ b` of `c` is set. -/
def bitSum (c : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => (if c / b % 2 = 1 then b else 0) + bitSum c bs

/-- The bit stages take a count below 64 whole. -/
theorem bitSum_sizes : ∀ c < 64, bitSum c VG.Impl.Rsa.PPC64LE.RecoverDet.bitSizes = c := by decide

/-- The bit stages of a shift `sh b` of `[j]`'s `L` words (by `b` bits, where the mask is set:
`G b`), by the bits of the count `c_b` in the slot `sl`: from `F a`, `[j] := F (a + bitSum c_b bs)`,
for `G b (F a) = F (a + b)`. -/
theorem bitStages_ok {B : Addr} {Z w N j L sl cb : Nat} (sh : Nat → Prog isa) (G : Nat → Nat → Nat)
    (F : Nat → Nat) (rs : List Reg) (hsl : sl + 4 ≤ 160) (hj8 : 160 ≤ arr w j)
    (hsh : ∀ (u : State) (b : Nat) (c : Bool), Ws u B Z w N → 0 < b → b < 64 → u.gpr .r9 = maskOf c →
      WP isa (sh b) u fun u' => wordsVal u'.mem B (arr w j) L =
          (if c then G b (wordsVal u.mem B (arr w j) L) else wordsVal u.mem B (arr w j) L) ∧
        Outside B (arr w j) (8 * L) u.mem u'.mem ∧ Ws u' B Z w N ∧ Keep rs u u')
    (hG : ∀ a b, G b (F a) = F (a + b)) (hL : 8 * L ≤ 8 * L) :
    ∀ (bs : List Nat) (s : State) (a : Nat), (∀ b ∈ bs, ∃ k, b = 2 ^ k ∧ k < 6) → Ws s B Z w N →
      slot s.mem B sl = cb → wordsVal s.mem B (arr w j) L = F a →
      WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.bitStages sl sh bs) s fun t =>
        wordsVal t.mem B (arr w j) L = F (a + bitSum cb bs) ∧ Outside B (arr w j) (8 * L) s.mem t.mem ∧
        Ws t B Z w N ∧ Keep (([.r0, .r3, .r9, .r10] : List Reg) ++ rs) s t
  | [], s, a, _, h, _, h0 => by
    unfold VG.Impl.Rsa.PPC64LE.RecoverDet.bitStages
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem) (by prun) (by decide)) fun t ⟨tm, tk⟩ =>
      ⟨by rw [tm, h0]; rfl, by rw [tm]; exact Outside.refl _ _ _ _, h.of_keep tk, tk.mono (by simp)⟩
  | b :: bs, s, a, hbs, h, hslot, h0 => by
    obtain ⟨k, rfl, hk⟩ := hbs b (List.mem_cons_self ..)
    have hk15 : 2 ^ k < 2 ^ 15 := Nat.pow_lt_pow_right (by decide) (by omega)
    have hk64 : 2 ^ k < 64 := Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hk) (by decide)
    unfold VG.Impl.Rsa.PPC64LE.RecoverDet.bitStages
    simp only [seqs]
    refine WP.seq (WP.mono (bitMask_ok h hsl hslot hk15) fun u1 ⟨⟨r9, m1⟩, k1⟩ => ?_)
    have h1 := h.of_keep k1
    refine WP.seq (WP.mono (hsh u1 (2 ^ k) _ h1 Nat.one_le_two_pow hk64 r9) fun u2 ⟨v2, o2, h2, k2⟩ => ?_)
    have slot2 : slot u2.mem B sl = cb := by
      rw [← hslot, ← m1]; exact o2.w32 (by omega_arith) (by omega_arith)
    have v2' : wordsVal u2.mem B (arr w j) L = F (a + (if cb / 2 ^ k % 2 = 1 then 2 ^ k else 0)) := by
      rw [v2, m1, h0]
      by_cases hb : cb / 2 ^ k % 2 = 1
      · simp only [hb, decide_true, ite_true, hG]
      · simp only [hb, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]
    refine WP.mono (bitStages_ok sh G F rs hsl hj8 hsh hG hL bs u2 _ (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
      h2 slot2 v2') fun t ⟨vt, ot, ht, kt⟩ => ⟨?_, ?_, ht, ?_⟩
    · rw [vt, bitSum, Nat.add_assoc]
    · rw [m1] at o2; exact o2.trans ot
    · exact ((k1.trans k2).trans kt).mono fun r hr => by
        simp only [List.mem_append] at hr ⊢
        rcases hr with (h | h) | (h | h) <;> first | exact .inl h | exact .inr h

/-- The registers the shifts by a count change. -/
abbrev shRegs : List Reg := [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem sizes_pows : ∀ b ∈ VG.Impl.Rsa.PPC64LE.RecoverDet.bitSizes, ∃ k, b = 2 ^ k ∧ k < 6 := by
  intro b hb
  simp only [VG.Impl.Rsa.PPC64LE.RecoverDet.bitSizes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨5, rfl, by decide⟩
  · exact ⟨4, rfl, by decide⟩
  · exact ⟨3, rfl, by decide⟩
  · exact ⟨2, rfl, by decide⟩
  · exact ⟨1, rfl, by decide⟩
  · exact ⟨0, rfl, by decide⟩

theorem keep_sh {s t : State} {rs : List Reg} (h : Keep rs s t) (hr : ∀ r ∈ rs, r ∈ shRegs := by decide) :
    Keep shRegs s t := h.mono hr

/-- `shrBy j sw sb`, for `w = 2 L`, `L ≥ 2`, the counts `c_w < L` and `c_b < 64` in the slots `sw`
and `sb`: `[j]`'s `L` words := `X / 2^(64 c_w + c_b)`. -/
theorem shrBy_ok {s : State} {B : Addr} {Z w N j L sw sb cw cb : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hwL : w = 2 * L) (hL : 2 ≤ L) (hsw : sw + 4 ≤ 160) (hsb : sb + 4 ≤ 160)
    (hcw : slot s.mem B sw = cw) (hcb : slot s.mem B sb = cb) (cwL : cw < L) (cb64 : cb < 64) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shrBy j sw sb) s fun t =>
      wordsVal t.mem B (arr w j) L = wordsVal s.mem B (arr w j) L / 2 ^ (64 * cw + cb) ∧
      Outside B (arr w j) (8 * L) s.mem t.mem ∧ Ws t B Z w N ∧ Keep shRegs s t := by
  have hj8 : 160 ≤ arr w j := Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (j * S w)
  generalize hX : wordsVal s.mem B (arr w j) L = X
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.shrBy
  refine WP.seq (WP.mono (wordStages_ok (VG.Impl.Rsa.PPC64LE.RecoverDet.shrWords j) (fun k V => V / 2 ^ (64 * k))
    (fun a => X / 2 ^ (64 * a)) (.r7 :: wlRegs) h hwL hL cwL hsw hcw hj8 (by decide)
    (fun u k c hu h1 hk h11 h9 h12 => shrWords_ok hu hj hN hwL h1 hk h11 h9 h12)
    (fun a k => by rw [VG.Proof.Bignum.ShiftStages.div_pow_add, Nat.mul_add])
    (by rw [hX, Nat.mul_zero, Nat.pow_zero, Nat.div_one])) fun s1 ⟨v1, o1, h1, k1⟩ => ?_)
  have slot1 : slot s1.mem B sb = cb := by rw [← hcb]; exact o1.w32 (by omega_arith) (by omega_arith)
  refine WP.mono (bitStages_ok (VG.Impl.Rsa.PPC64LE.RecoverDet.shrBits j) (fun b V => V / 2 ^ b)
    (fun a => X / 2 ^ (64 * cw) / 2 ^ a) (.r7 :: wlRegs) hsb hj8
    (fun u b c hu hb hb' h9 => shrBits_ok hu hj hN hwL hL hb hb' h9)
    (fun a b => by rw [VG.Proof.Bignum.ShiftStages.div_pow_add]) (Nat.le_refl _) _ s1 0 sizes_pows h1
    slot1 (by rw [v1, Nat.pow_zero, Nat.div_one])) fun t ⟨vt, ot, ht, kt⟩ =>
      ⟨by rw [vt, Nat.zero_add, bitSum_sizes cb cb64, VG.Proof.Bignum.ShiftStages.div_pow_add], o1.trans ot, ht,
        keep_sh (k1.trans kt)⟩

/-- `shlBy j sw sb bits`, for `w = 2 L`, `L ≥ 2`, the counts `c_w < L` and `c_b < 64` in the slots `sw`
and `sb`: `[j]`'s `L` words := `X 2^(64 c_w + c_b) mod 2^(64 L)`, or without `c_b` unless `bits`. -/
theorem shlBy_ok {s : State} {B : Addr} {Z w N j L sw sb cw cb : Nat} (bits : Bool) (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (hwL : w = 2 * L) (hL : 2 ≤ L) (hsw : sw + 4 ≤ 160) (hsb : sb + 4 ≤ 160)
    (hcw : slot s.mem B sw = cw) (hcb : slot s.mem B sb = cb) (cwL : cw < L) (cb64 : bits = true → cb < 64) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shlBy j sw sb bits) s fun t =>
      wordsVal t.mem B (arr w j) L =
        wordsVal s.mem B (arr w j) L * 2 ^ (64 * cw + (if bits then cb else 0)) % 2 ^ (64 * L) ∧
      Outside B (arr w j) (8 * L) s.mem t.mem ∧ Ws t B Z w N ∧ Keep shRegs s t := by
  have hj8 : 160 ≤ arr w j := Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (j * S w)
  generalize hX : wordsVal s.mem B (arr w j) L = X
  have hXL : X < 2 ^ (64 * L) := hX ▸ wordsVal_lt _ _ _ _
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.shlBy
  refine WP.seq (WP.mono (wordStages_ok (VG.Impl.Rsa.PPC64LE.RecoverDet.shlWords j)
    (fun k V => V * 2 ^ (64 * k) % 2 ^ (64 * L)) (fun a => X * 2 ^ (64 * a) % 2 ^ (64 * L)) (.r7 :: wlRegs) h hwL hL
    cwL hsw hcw hj8 (by decide) (fun u k c hu h1 hk h11 h9 h12 => shlWords_ok hu hj hN hwL h1 hk h11 h9 h12)
    (fun a k => by rw [VG.Proof.Bignum.ShiftStages.mul_pow_add_mod, Nat.mul_add])
    (by rw [hX, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hXL])) fun s1 ⟨v1, o1, h1, k1⟩ => ?_)
  cases bits with
  | false =>
    show WP isa (.block []) s1 _
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s1.mem) (by prun) (by decide)) fun t ⟨tm, tk⟩ =>
      ⟨by rw [tm, v1]; simp, by rw [tm]; exact o1, h1.of_keep tk, keep_sh (k1.trans tk)⟩
  | true =>
    have slot1 : slot s1.mem B sb = cb := by rw [← hcb]; exact o1.w32 (by omega_arith) (by omega_arith)
    refine WP.mono (bitStages_ok (VG.Impl.Rsa.PPC64LE.RecoverDet.shlBits j) (fun b V => V * 2 ^ b % 2 ^ (64 * L))
      (fun a => X * 2 ^ (64 * cw) % 2 ^ (64 * L) * 2 ^ a % 2 ^ (64 * L)) (.r7 :: .r10 :: wlRegs) hsb hj8
      (fun u b c hu hb hb' h9 => shlBits_ok hu hj hN hwL hL hb hb' h9)
      (fun a b => by rw [VG.Proof.Bignum.ShiftStages.mul_pow_add_mod]) (Nat.le_refl _) _ s1 0
      sizes_pows h1 slot1 (by rw [v1, Nat.pow_zero, Nat.mul_one, Nat.mod_mod])) fun t ⟨vt, ot, ht, kt⟩ =>
        ⟨by rw [vt, Nat.zero_add, bitSum_sizes cb (cb64 rfl), VG.Proof.Bignum.ShiftStages.mul_pow_add_mod]; rfl,
          o1.trans ot, ht, keep_sh (k1.trans kt)⟩

/-! ## Trailing zeros -/

section TZ
open VG.Proof.Bignum.ShiftStages (tz dvd_iff tz_div tz_spec tz_lt dvd_gcd_iff)

/-- Words above a number's trailing zeros leave them. -/
theorem tz_add_high {a b k : Nat} (ha : a ≠ 0) (hak : a < 2 ^ k) : tz (a + 2 ^ k * b) = tz a := by
  have h0 : a + 2 ^ k * b ≠ 0 := by omega
  have ta : tz a < k := tz_lt (by omega) hak
  apply Nat.le_antisymm
  · refine Nat.le_of_not_lt fun c => ?_
    have d1 : 2 ^ (tz a + 1) ∣ a + 2 ^ k * b := (dvd_iff h0 (tz a + 1)).mpr (by omega)
    have d2 : 2 ^ (tz a + 1) ∣ 2 ^ k * b := Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 (by omega)) b
    have d3 : 2 ^ (tz a + 1) ∣ a := (Nat.dvd_add_right d2).mp (Nat.add_comm a (2 ^ k * b) ▸ d1)
    have := (dvd_iff ha _).mp d3; omega
  · exact (dvd_iff h0 _).mp (Nat.dvd_add ((dvd_iff ha _).mpr (Nat.le_refl _))
      (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 (by omega)) b))

/-- `2^k y` has `k` more trailing zeros than `y`. -/
theorem tz_mul_pow {k y : Nat} (hy : y ≠ 0) : tz (2 ^ k * y) = k + tz y := by
  have h0 : 2 ^ k * y ≠ 0 := Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)) hy
  apply Nat.le_antisymm
  · refine Nat.le_of_not_lt fun c => ?_
    have d := (dvd_iff h0 (k + (tz y + 1))).mpr (by omega)
    rw [Nat.pow_add] at d
    have := (dvd_iff hy _).mp (Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos k) d)
    omega
  · refine (dvd_iff h0 _).mp ?_
    rw [Nat.pow_add]
    exact Nat.mul_dvd_mul_left _ ((dvd_iff hy _).mpr (Nat.le_refl _))

/-- The trailing zeros of `u ∨ x` are those of `gcd(u, x)`, for `u ≠ 0`. -/
theorem tz_or_gcd {u x : Nat} (hu : u ≠ 0) : tz (u ||| x) = tz (Nat.gcd u x) := by
  have h0 : u ||| x ≠ 0 := fun h => hu (Nat.or_eq_zero_iff.mp h).1
  have hg : Nat.gcd u x ≠ 0 := Nat.gcd_ne_zero_left hu
  have key : ∀ s, 2 ^ s ∣ u ||| x ↔ 2 ^ s ∣ Nat.gcd u x := fun s => by
    rw [← dvd_gcd_iff, Nat.dvd_iff_mod_eq_zero, Nat.or_mod_two_pow, Nat.or_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
      Nat.dvd_iff_mod_eq_zero]
  apply Nat.le_antisymm
  · exact (dvd_iff hg _).mp ((key _).mp ((dvd_iff h0 _).mpr (Nat.le_refl _)))
  · exact (dvd_iff h0 _).mp ((key _).mpr ((dvd_iff hg _).mpr (Nat.le_refl _)))

/-- A number's lowest word that is not zero, and its trailing zeros. -/
theorem tz_word {Y : Nat} (hY : Y ≠ 0) :
    Y / 2 ^ (64 * (tz Y / 64)) % 2 ^ 64 ≠ 0 ∧ tz (Y / 2 ^ (64 * (tz Y / 64)) % 2 ^ 64) = tz Y % 64 := by
  have hle : 64 * (tz Y / 64) ≤ tz Y := Nat.mul_div_le _ _
  have hm0 : Y / 2 ^ (64 * (tz Y / 64)) ≠ 0 := by
    intro h
    have := Nat.div_mul_cancel ((dvd_iff hY _).mpr hle)
    rw [h, Nat.zero_mul] at this
    exact hY this.symm
  have htm : tz (Y / 2 ^ (64 * (tz Y / 64))) = tz Y % 64 := by rw [tz_div hY hle]; omega
  generalize Y / 2 ^ (64 * (tz Y / 64)) = m at hm0 htm
  have hsplit := Nat.mod_add_div m (2 ^ 64)
  have hlo : m % 2 ^ 64 ≠ 0 := by
    intro h
    have : 2 ^ 64 ∣ m := Nat.dvd_of_mod_eq_zero h
    have := (dvd_iff hm0 _).mp this
    omega
  refine ⟨hlo, ?_⟩
  rw [← htm]
  conv => rhs; rw [← hsplit]
  rw [tz_add_high hlo (Nat.mod_lt _ (by decide))]

end TZ

/-! ## The trailing zero words, by a scan -/

section Scan
open VG.Proof.Bignum.ShiftStages (tz tz_lt tz_spec)

/-- The mask of a word that is zero: `((0 - y) | y) >>> 63 - 1`. -/
theorem zmask (y : BitVec 64) :
    (BitVec.ofNat 64 0 - y ||| y) >>> 63 - BitVec.ofNat 64 1 = if y = 0#64 then BitVec.allOnes 64 else 0#64 := by
  rw [BitVec.or_comm, show BitVec.ofNat 64 0 = 0#64 from rfl, nz_bit]
  by_cases hy : y = 0#64 <;> (simp only [hy, ↓reduceIte]) <;> decide

/-- The scan's body. -/
abbrev tzBody : List Instr :=
  [.load .d .r0 .r5 0, .load .d .r3 .r6 0, .logic .or .r0 .r0 .r3, .logic .and .r3 .r0 .r9,
    .logic .or .r11 .r11 .r3, .li .r3 0, .sub .r3 .r3 .r0, .logic .or .r3 .r3 .r0, .lsr .d .r3 .r3 63,
    .subi .r3 .r3 1, .logic .and .r9 .r9 .r3, .li .r3 1, .logic .and .r3 .r9 .r3, .add .r10 .r10 .r3,
    .addi .r5 .r5 8, .addi .r6 .r6 8]

/-- A word of `U ∨ X`. -/
theorem or_word {m : Mem} {B : Addr} {dA dB L i : Nat} (hi : i < L) :
    (wordsVal m B dA L ||| wordsVal m B dB L) / 2 ^ (64 * i) % 2 ^ 64 =
      (word m B (dA + 8 * i) ||| word m B (dB + 8 * i)).toNat := by
  rw [BitVec.toNat_or, ← wordsVal_word hi, ← wordsVal_word hi, Nat.or_div_two_pow, Nat.or_mod_two_pow]

/-- The low `i + 1` words: the low `i` and word `i`. -/
theorem mod_succ_word (Y i : Nat) :
    Y % 2 ^ (64 * (i + 1)) = Y % 2 ^ (64 * i) + 2 ^ (64 * i) * (Y / 2 ^ (64 * i) % 2 ^ 64) := by
  rw [show 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 by rw [← Nat.pow_add]; congr 1, Nat.mod_mul]

/-- A step of the scan, in numbers: the low `i + 1` words `Y' = Y_i + 2^(64 i) y`. -/
theorem scan_step {Yi y i : Nat} (hlo : Yi < 2 ^ (64 * i)) (hy : y < 2 ^ 64) :
    (Yi + 2 ^ (64 * i) * y = 0 ↔ Yi = 0 ∧ y = 0) ∧
    (Yi = 0 → y ≠ 0 → tz (Yi + 2 ^ (64 * i) * y) / 64 = i ∧
      (Yi + 2 ^ (64 * i) * y) / 2 ^ (64 * (tz (Yi + 2 ^ (64 * i) * y) / 64)) % 2 ^ 64 = y) ∧
    (Yi ≠ 0 → tz (Yi + 2 ^ (64 * i) * y) = tz Yi ∧
      (Yi + 2 ^ (64 * i) * y) / 2 ^ (64 * (tz Yi / 64)) % 2 ^ 64 = Yi / 2 ^ (64 * (tz Yi / 64)) % 2 ^ 64) := by
  have hp := Nat.two_pow_pos (64 * i)
  refine ⟨⟨fun h => ?_, fun ⟨h1, h2⟩ => by rw [h1, h2]; rfl⟩, fun h0 hy0 => ?_, fun h0 => ?_⟩
  · have : 2 ^ (64 * i) * y = 0 := by omega
    exact ⟨by omega, (Nat.mul_eq_zero.mp this).resolve_left (by omega)⟩
  · subst h0
    have htz : tz (0 + 2 ^ (64 * i) * y) / 64 = i := by
      rw [Nat.zero_add, tz_mul_pow hy0]
      have := tz_lt (Nat.pos_of_ne_zero hy0) hy
      omega
    refine ⟨htz, ?_⟩
    rw [htz, Nat.zero_add, Nat.mul_div_cancel_left _ hp, Nat.mod_eq_of_lt hy]
  · refine ⟨tz_add_high h0 hlo, ?_⟩
    have hq : tz Yi / 64 < i := by have := tz_lt (Nat.pos_of_ne_zero h0) hlo; omega
    obtain ⟨e, he⟩ : ∃ e, i = tz Yi / 64 + 1 + e := ⟨i - (tz Yi / 64 + 1), by omega⟩
    rw [he, show 64 * (tz Yi / 64 + 1 + e) = 64 * (tz Yi / 64) + 64 * (1 + e) by omega, Nat.pow_add,
      Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      show 2 ^ (64 * (1 + e)) = 2 ^ 64 * 2 ^ (64 * e) by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- The scan: `r10 :=` the trailing zero words of `Y = U ∨ X` (`L` words at `dA` and `dB`), `L`
for `Y = 0`, and `r11 :=` its lowest word that is not zero. -/
theorem tzScan_ok {s : State} {B : Addr} {Z dA dB L : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dA) (h6 : s.gpr .r6 = off B dB) (h8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (h9 : s.gpr .r9 = BitVec.allOnes 64) (h10 : s.gpr .r10 = BitVec.ofNat 64 0)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 0) (hL : 1 ≤ L) (hL' : L < 2 ^ 32) (hA : dA + 8 * L ≤ Z)
    (hB : dB + 8 * L ≤ Z) :
    WP isa (countLoop .r8 tzBody) s fun t =>
      t.gpr .r10 = BitVec.ofNat 64 (if (wordsVal s.mem B dA L ||| wordsVal s.mem B dB L) = 0 then L
        else tz (wordsVal s.mem B dA L ||| wordsVal s.mem B dB L) / 64) ∧
      t.gpr .r11 = BitVec.ofNat 64 (if (wordsVal s.mem B dA L ||| wordsVal s.mem B dB L) = 0 then 0
        else (wordsVal s.mem B dA L ||| wordsVal s.mem B dB L) /
          2 ^ (64 * (tz (wordsVal s.mem B dA L ||| wordsVal s.mem B dB L) / 64)) % 2 ^ 64) ∧
      t.mem = s.mem ∧ Keep [.r0, .r3, .r5, .r6, .r8, .r9, .r10, .r11] s t := by
  have hnw := hs.nowrap
  generalize hY : (wordsVal s.mem B dA L ||| wordsVal s.mem B dB L) = Y
  have hYL : Y < 2 ^ (64 * L) := hY ▸ Nat.or_lt_two_pow (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dA + 8 * i) ∧ t.gpr .r6 = off B (dB + 8 * i) ∧ t.mem = s.mem ∧
      t.gpr .r9 = (if Y % 2 ^ (64 * i) = 0 then BitVec.allOnes 64 else 0#64) ∧
      t.gpr .r10 = BitVec.ofNat 64 (if Y % 2 ^ (64 * i) = 0 then i else tz (Y % 2 ^ (64 * i)) / 64) ∧
      t.gpr .r11 = BitVec.ofNat 64 (if Y % 2 ^ (64 * i) = 0 then 0
        else Y % 2 ^ (64 * i) / 2 ^ (64 * (tz (Y % 2 ^ (64 * i)) / 64)) % 2 ^ 64) ∧
      Keep [.r0, .r3, .r5, .r6, .r8, .r9, .r10, .r11] s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, jm, j9, j10, j11, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, rfl, by simp [h9, Nat.mod_one], by simp [h10, Nat.mod_one],
      by simp [h11, Nat.mod_one], Keep.refl _ _⟩ h8)
    fun t ⟨_, _, jm, _, j10, j11, jk⟩ => ⟨by rw [j10, Nat.mod_eq_of_lt hYL], by rw [j11, Nat.mod_eq_of_lt hYL],
      jm, jk⟩
  have hst : WP isa (.block (tzBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dA + 8 * i + 8) ∧ t'.gpr .r6 = off B (dB + 8 * i + 8) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧ t'.mem = t.mem ∧
        t'.gpr .r9 = t.gpr .r9 &&& ((BitVec.ofNat 64 0 - (word t.mem B (dA + 8 * i) ||| word t.mem B (dB + 8 * i)) |||
          (word t.mem B (dA + 8 * i) ||| word t.mem B (dB + 8 * i))) >>> 63 - BitVec.ofNat 64 1) ∧
        t'.gpr .r10 = t.gpr .r10 + (t'.gpr .r9 &&& BitVec.ofNat 64 1) ∧
        t'.gpr .r11 = t.gpr .r11 ||| ((word t.mem B (dA + 8 * i) ||| word t.mem B (dB + 8 * i)) &&& t.gpr .r9)) ∧
      Keep [.r0, .r3, .r5, .r6, .r8, .r9, .r10, .r11] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j5, j6, (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dB + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l8, lm, l9, l10, l11⟩, lk⟩ => ?_
  simp only [jm] at l9 l11
  have hw := or_word (m := s.mem) (B := B) (dA := dA) (dB := dB) hi
  rw [hY] at hw
  generalize hy : (word s.mem B (dA + 8 * i) ||| word s.mem B (dB + 8 * i)) = y at l9 l11 hw
  rw [zmask] at l9
  have hsucc : Y % 2 ^ (64 * (i + 1)) = Y % 2 ^ (64 * i) + 2 ^ (64 * i) * y.toNat := by rw [mod_succ_word Y i, hw]
  have hlo : Y % 2 ^ (64 * i) < 2 ^ (64 * i) := Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨z1, z2, z3⟩ := scan_step hlo y.isLt
  have hy0 : y = 0#64 ↔ y.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  generalize Y % 2 ^ (64 * i) = Yi at j9 j10 j11 hlo hsucc z1 z2 z3
  have hp : 2 ^ (64 * i) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
  refine ⟨⟨?_, ?_, by rw [lm, jm], ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l6, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · -- `r9`: all ones while every word so far is zero.
    rw [l9, j9, hsucc]
    by_cases hYi : Yi = 0
    · subst hYi
      by_cases hyz : y = 0#64
      · subst hyz; simp
      · have hne : 2 ^ (64 * i) * y.toNat ≠ 0 := Nat.mul_ne_zero hp (hy0.not.mp hyz)
        simp [hyz, hne]
    · simp [hYi]
  · -- `r10`.
    rw [l10, l9, j9, j10, hsucc]
    by_cases hYi : Yi = 0
    · subst hYi
      by_cases hyz : y = 0#64
      · subst hyz
        (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) <;> omega_arith
      · have hyt := hy0.not.mp hyz
        have hne : 2 ^ (64 * i) * y.toNat ≠ 0 := Nat.mul_ne_zero hp hyt
        rw [(z2 rfl hyt).1]
        simp [hyz, hne]
    · rw [(z3 hYi).1]
      simp [hYi]
  · -- `r11`: the lowest word that is not zero.
    rw [l11, j9, j11, hsucc]
    by_cases hYi : Yi = 0
    · subst hYi
      by_cases hyz : y = 0#64
      · subst hyz; simp
      · have hyt := hy0.not.mp hyz
        have hne : 2 ^ (64 * i) * y.toNat ≠ 0 := Nat.mul_ne_zero hp hyt
        rw [(z2 rfl hyt).2]
        apply BitVec.eq_of_toNat_eq
        simp only [hne, ↓reduceIte, BitVec.toNat_ofNat, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_allOnes,
          Nat.zero_add, Nat.zero_mod, Nat.zero_or, Nat.and_two_pow_sub_one_eq_mod]
    · rw [(z3 hYi).1, (z3 hYi).2]
      simp [hYi]

end Scan

/-! ## The trailing zeros of a word, by stages -/

section Stages
open VG.Proof.Bignum.ShiftStages (tz stage_tz greedy greedy_cons greedy_nil greedy_pows pows)

/-- A word shifted up by `64 - b` is zero exactly when its low `b` bits are. -/
theorem shl_zero_iff (z : BitVec 64) {b : Nat} (hb' : b ≤ 64) : z <<< (64 - b) = 0#64 ↔ z.toNat % 2 ^ b = 0 := by
  have hP : 2 ^ b * 2 ^ (64 - b) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  have e : (z <<< (64 - b)).toNat = z.toNat % 2 ^ b * 2 ^ (64 - b) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ← hP, Nat.mul_mod_mul_right]
  constructor
  · intro h; have := congrArg BitVec.toNat h
    rw [e] at this
    exact (Nat.mul_eq_zero.mp this).resolve_right (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  · intro h; apply BitVec.eq_of_toNat_eq; rw [e, h, Nat.zero_mul]; rfl

/-- A stage of a word's trailing zeros, `b = 2^lg`: `r11 := r11 >> b` and `r10 := r10 + b` if the
low `b` bits of `r11` are zero. -/
theorem tzStage_ok {s : State} {lg : Nat} (hlg : lg < 6) (z acc : BitVec 64) (h11 : s.gpr .r11 = z)
    (h10 : s.gpr .r10 = acc) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage (2 ^ lg) lg)) s fun u =>
      (u.gpr .r11 = (if z.toNat % 2 ^ 2 ^ lg = 0 then z >>> 2 ^ lg else z) ∧
        u.gpr .r10 = acc + BitVec.ofNat 64 (if z.toNat % 2 ^ 2 ^ lg = 0 then 2 ^ lg else 0) ∧ u.mem = s.mem) ∧
      Keep [.r0, .r3, .r9, .r10, .r11] s u := by
  have h1 : 1 ≤ 2 ^ lg := Nat.one_le_two_pow
  have h64 : 2 ^ lg < 64 := Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hlg) (by decide)
  refine WP.keep _ ?_ (by rfl)
  prun [VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage, h11, h10, exec_lsl (show 64 - 2 ^ lg < 64 by omega),
    exec_lsl (show lg < 64 by omega), exec_lsr_d (show 2 ^ lg < 64 by omega)]
  have e1 : (z <<< (64 - 2 ^ lg) ||| 0#64 - z <<< (64 - 2 ^ lg)) >>> 63 ^^^ 1#64 =
      BitVec.ofNat 64 (if z.toNat % 2 ^ 2 ^ lg = 0 then 1 else 0) := by
    rw [nz_bit]
    by_cases hc : z.toNat % 2 ^ 2 ^ lg = 0
    · have hz := (shl_zero_iff z (b := 2 ^ lg) (by omega)).mpr hc
      simp only [hz, hc, ↓reduceIte]; rfl
    · have hz : ¬ z <<< (64 - 2 ^ lg) = 0#64 := fun h => hc ((shl_zero_iff z (by omega)).mp h)
      simp only [hz, hc, ↓reduceIte]; rfl
  rw [e1]
  by_cases hc : z.toNat % 2 ^ 2 ^ lg = 0
  · simp only [hc, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [show (0#64 - BitVec.ofNat 64 1 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes,
        BitVec.xor_comm (z >>> 2 ^ lg) z, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.one_mul]
  · simp only [hc, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [show (0#64 - BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, BitVec.xor_zero]
    · congr 1
      apply BitVec.eq_of_toNat_eq
      simp

/-- The stages `2^lg` for `lg ∈ lgs`, from `a ≤ T = tz z₀` trailing zeros taken (`r11 = z₀ / 2^a`,
`r10 = a`): `greedy` takes each that fits (`ShiftStages.stage_tz`). -/
theorem tzStages_ok {z0 : Nat} (hz0 : z0 ≠ 0) (hz : z0 < 2 ^ 64) :
    ∀ (lgs : List Nat) (s : State) (a : Nat), (∀ lg ∈ lgs, lg < 6) → a ≤ tz z0 →
      s.gpr .r11 = BitVec.ofNat 64 (z0 / 2 ^ a) → s.gpr .r10 = BitVec.ofNat 64 a →
      WP isa (.block (lgs.flatMap fun lg => VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage (2 ^ lg) lg)) s fun u =>
        u.gpr .r11 = BitVec.ofNat 64 (z0 / 2 ^ greedy (tz z0) (lgs.map (2 ^ ·)) a) ∧
        u.gpr .r10 = BitVec.ofNat 64 (greedy (tz z0) (lgs.map (2 ^ ·)) a) ∧ u.mem = s.mem ∧
        Keep [.r0, .r3, .r9, .r10, .r11] s u
  | [], s, a, _, _, h11, h10 => by
    rw [List.flatMap_nil]
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem) (by prun) (by decide)) fun t ⟨tm, tk⟩ =>
      ⟨by rw [tk.gpr .r11 (by decide), h11]; rfl, by rw [tk.gpr .r10 (by decide), h10]; rfl, tm, tk.mono (by simp)⟩
  | lg :: lgs, s, a, hl, ha, h11, h10 => by
    have hlg := hl lg (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (tzStage_ok hlg _ _ h11 h10) fun u ⟨⟨u11, u10, um⟩, uk⟩ => ?_)
    have hza : (BitVec.ofNat 64 (z0 / 2 ^ a)).toNat = z0 / 2 ^ a :=
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hz)]
    have hst := stage_tz hz0 ha (2 ^ lg)
    rw [hza] at u11 u10
    have e11 : u.gpr .r11 = BitVec.ofNat 64 (z0 / 2 ^ (if a + 2 ^ lg ≤ tz z0 then a + 2 ^ lg else a)) := by
      rw [u11]
      by_cases hc : a + 2 ^ lg ≤ tz z0
      · simp only [hst.mpr hc, hc, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hza, BitVec.toNat_ofNat,
          VG.Proof.Bignum.ShiftStages.div_pow_add, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hz)]
      · have hc' : ¬ z0 / 2 ^ a % 2 ^ 2 ^ lg = 0 := fun h => hc (hst.mp h)
        simp only [hc', hc, ↓reduceIte]
    have e10 : u.gpr .r10 = BitVec.ofNat 64 (if a + 2 ^ lg ≤ tz z0 then a + 2 ^ lg else a) := by
      rw [u10]
      by_cases hc : a + 2 ^ lg ≤ tz z0
      · simp only [hst.mpr hc, hc, ↓reduceIte, BitVec.ofNat_add]
      · have hc' : ¬ z0 / 2 ^ a % 2 ^ 2 ^ lg = 0 := fun h => hc (hst.mp h)
        simp [hc', hc]
    refine WP.mono (tzStages_ok hz0 hz lgs u _ (fun l h => hl l (List.mem_cons_of_mem _ h))
      (by split <;> omega) e11 e10) fun t ⟨t11, t10, tm, tk⟩ =>
        ⟨by rw [t11, List.map_cons, greedy_cons], by rw [t10, List.map_cons, greedy_cons], by rw [tm, um],
          (uk.trans tk).mono (by simp)⟩

end Stages

/-! ## The trailing zeros of two arrays' or -/

section TzW
open VG.Proof.Bignum.ShiftStages (tz tz_lt greedy_pows pows)
open VG.Proof.Rsa.KeyWorkspace (arr S)
open VG.Proof.Rsa.PPC64LE.Recover (slot_wne)

/-- The final block of `tzW`, as a store, the stages and a store. -/
theorem tzW_tail (sw sb : Nat) :
    ([.store .w .r10 .r31 sw, .li .r10 0] : List Instr) ++ VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage 32 5 ++
      VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage 16 4 ++ VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage 8 3 ++
      VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage 4 2 ++ VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage 2 1 ++
      VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage 1 0 ++ ([.store .w .r10 .r31 sb] : List Instr) =
    ([.store .w .r10 .r31 sw, .li .r10 0] : List Instr) ++
      (([5, 4, 3, 2, 1, 0] : List Nat).flatMap (fun lg => VG.Impl.Rsa.PPC64LE.RecoverDet.tzStage (2 ^ lg) lg) ++
        ([.store .w .r10 .r31 sb] : List Instr)) := rfl

/-- `tzW a b sw sb`, for `w = 2 L` and `Y = [a] ∨ [b]` (their `L` words) not zero: the slots
`sw := ⌊tz Y / 64⌋` and `sb := tz Y mod 64`. -/
theorem tzW_ok {s : State} {B : Addr} {Z w N a b L sw sb : Nat} (h : Ws s B Z w N) (ha : a < N) (hb : b < N)
    (hN : N ≤ 256) (hwL : w = 2 * L) (hL : 1 ≤ L) (hsw : sw + 4 ≤ 160) (hsb : sb + 4 ≤ 160)
    (hss : sw + 4 ≤ sb ∨ sb + 4 ≤ sw)
    (hY : (wordsVal s.mem B (arr w a) L ||| wordsVal s.mem B (arr w b) L) ≠ 0) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.tzW a b sw sb) s fun t =>
      slot t.mem B sw = tz (wordsVal s.mem B (arr w a) L ||| wordsVal s.mem B (arr w b) L) / 64 ∧
      slot t.mem B sb = tz (wordsVal s.mem B (arr w a) L ||| wordsVal s.mem B (arr w b) L) % 64 ∧
      KeyWorkspace.Keep B w [] [sw, sb] s.mem t.mem ∧ Ws t B Z w N ∧ Keep shRegs s t := by
  have := h.wle
  have hnw := h.nowrap
  have hz : 160 ≤ Z := h.hdr_le
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  simp only [S] at fa fb
  have e7 : BitVec.ofNat 64 w >>> 1 = BitVec.ofNat 64 L := by rw [hwL]; exact mont_ofNat_shr1 (by omega_arith)
  generalize hYd : (wordsVal s.mem B (arr w a) L ||| wordsVal s.mem B (arr w b) L) = Y at hY ⊢
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.tzW
  simp only [seqs]
  -- The setup.
  have hb1 : WP isa (.block (ptr .r5 a ++ ptr .r6 b ++ VG.Impl.Rsa.PPC64LE.RecoverDet.lenW ++
      [.addi .r8 .r7 0, .li .r9 0, .subi .r9 .r9 1, .li .r10 0, .li .r11 0])) s fun u =>
      (u.gpr .r5 = off B (arr w a) ∧ u.gpr .r6 = off B (arr w b) ∧ u.gpr .r8 = BitVec.ofNat 64 L ∧
        u.gpr .r9 = BitVec.allOnes 64 ∧ u.gpr .r10 = BitVec.ofNat 64 0 ∧ u.gpr .r11 = BitVec.ofNat 64 0 ∧
        u.mem = s.mem) ∧ Keep [.r5, .r6, .r7, .r8, .r9, .r10, .r11] s u := by
    rw [List.append_assoc, List.append_assoc]
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show a < 2 ^ 15 by omega_arith) ?_
    have h' := h.of_keep (Keep.write s .r5 (off B (arr w a)))
    refine ptr_ok h' (r := .r6) (by decide) (by decide) (by decide) (show b < 2 ^ 15 by omega_arith) ?_
    refine WP.mono (WP.keep [.r7, .r8, .r9, .r10, .r11] (Q := fun u => u.gpr .r8 = BitVec.ofNat 64 L ∧
      u.gpr .r9 = BitVec.allOnes 64 ∧ u.gpr .r10 = BitVec.ofNat 64 0 ∧ u.gpr .r11 = BitVec.ofNat 64 0 ∧
      u.mem = s.mem) (by
      prun [VG.Impl.Rsa.PPC64LE.RecoverDet.lenW, gpr_write, mem_write, h.r29, e7]
      and_intros <;> first | exact BitVec.add_zero _ | decide | rfl) (by decide))
      fun u ⟨⟨u8, u9, u10, u11, um⟩, uk⟩ => ⟨⟨by rw [uk.gpr .r5 (by decide)]; simp [gpr_write],
        by rw [uk.gpr .r6 (by decide)]; simp [gpr_write], u8, u9, u10, u11, by rw [um]⟩,
        (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans uk).mono (by decide)⟩
  refine WP.seq (WP.mono hb1 fun s1 ⟨⟨r5, r6, r8, r9, r10, r11, m1⟩, k1⟩ => ?_)
  have hs1 := h.of_keep k1
  refine WP.seq (WP.mono (tzScan_ok (dA := arr w a) (dB := arr w b) (L := L) hs1.scr r5 r6 r8 r9 r10 r11 hL
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s2 ⟨v10, v11, m2, k2⟩ => ?_)
  rw [m1, hYd] at v10 v11
  simp only [hY, ↓reduceIte] at v10 v11
  have hs2 := hs1.of_keep k2
  obtain ⟨z0, tz0⟩ := tz_word hY
  generalize hz0 : Y / 2 ^ (64 * (tz Y / 64)) % 2 ^ 64 = z at z0 tz0 v11
  have hzl : z < 2 ^ 64 := hz0 ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  have hYL : Y < 2 ^ (64 * L) := hYd ▸ Nat.or_lt_two_pow (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _)
  have hq : tz Y / 64 < L := by have := tz_lt (Nat.pos_of_ne_zero hY) hYL; omega
  have htz : tz Y % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [tzW_tail, WP.block_append_iff]
  -- The count of words, stored.
  refine WP.mono (WP.keep [.r10] (Q := fun u => u.mem = s2.mem.writeW (off B sw) ((s2.gpr .r10).setWidth 32) ∧
    u.gpr .r10 = BitVec.ofNat 64 0 ∧ u.gpr .r11 = s2.gpr .r11) (by
      prun [hs2.r31, hs2.scr.st (show sw + 4 ≤ Z by omega_arith),
        exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sw < 2 ^ 15 by omega_arith)]) (by rfl))
    fun s3 ⟨⟨m3, r10', r11'⟩, k3⟩ => ?_
  rw [WP.block_append_iff]
  have hs3 := hs2.of_keep k3
  refine WP.mono (tzStages_ok z0 hzl [5, 4, 3, 2, 1, 0] s3 0 (by decide) (Nat.zero_le _)
    (by rw [r11', v11, Nat.pow_zero, Nat.div_one]) r10') fun s4 ⟨_, u10, m4, k4⟩ => ?_
  have hs4 := hs3.of_keep k4
  have hg : VG.Proof.Bignum.ShiftStages.greedy (tz z) (([5, 4, 3, 2, 1, 0] : List Nat).map (2 ^ ·)) 0 = tz Y % 64 := by
    rw [show (([5, 4, 3, 2, 1, 0] : List Nat).map (2 ^ ·)) = pows 5 from rfl, tz0]
    exact greedy_pows 5 _ 0 (Nat.zero_le _) (by omega)
  rw [hg] at u10
  -- The count of bits, stored.
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s4.mem.writeW (off B sb) ((s4.gpr .r10).setWidth 32)) (by
      prun [hs4.r31, hs4.scr.st (show sb + 4 ≤ Z by omega_arith),
        exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sb < 2 ^ 15 by omega_arith)]) (by rfl))
    fun t ⟨mt, kt⟩ => ?_
  have hsw' : slot s3.mem B sw = tz Y / 64 := by
    rw [m3, slot_write_self, BitVec.toNat_setWidth, v10, BitVec.toNat_ofNat]
    omega_arith
  refine ⟨?_, ?_, ?_, hs4.of_keep kt, keep_sh (((k1.trans k2).trans ((k3.trans k4).trans kt)))⟩
  · rw [mt, slot_wne _ _ _ hss.symm (by omega_arith) (by omega_arith), m4, hsw']
  · rw [mt, slot_write_self, BitVec.toNat_setWidth, u10, BitVec.toNat_ofNat]
    omega_arith
  · have e1 : KeyWorkspace.Keep B w [] [sw, sb] s.mem s3.mem := by
      rw [m3, m2, m1]; exact keep_slot _ _ (by simp) (by omega_arith)
    have e2 : KeyWorkspace.Keep B w [] [sw, sb] s3.mem t.mem := by
      rw [mt, m4]; exact keep_slot _ _ (by simp) (by omega_arith)
    exact e1.trans e2

end TzW

/-! ## The leading zero words of an array -/

section ClzW
open VG.Proof.Rsa.KeyWorkspace (arr S)
open VG.Proof.Rsa.PPC64LE.Recover (slot_wne)

/-- The scan's body. -/
abbrev clzBody : List Instr :=
  [.load .d .r0 .r5 0, .li .r3 0, .sub .r3 .r3 .r0, .logic .or .r3 .r3 .r0, .lsr .d .r3 .r3 63,
    .subi .r3 .r3 1, .logic .and .r9 .r9 .r3, .li .r3 1, .logic .and .r3 .r9 .r3, .add .r10 .r10 .r3,
    .subi .r5 .r5 8]

/-- What the leading zero words `r` of `T`, of `i` words, are: all `i` for `T = 0`, else `T`'s top
word that is not zero is word `i - r - 1`. -/
def ClzOf (T i r : Nat) : Prop :=
  r ≤ i ∧ (T = 0 → r = i) ∧ (T ≠ 0 → 2 ^ (64 * (i - r - 1)) ≤ T ∧ T < 2 ^ (64 * (i - r)))

/-- A step of the scan, a word `y` below `T`: the count goes on while `T` and `y` are zero. -/
theorem clz_step {T y i r : Nat} (h : ClzOf T i r) (hy : y < 2 ^ 64) :
    ClzOf (y + 2 ^ 64 * T) (i + 1) (if T = 0 ∧ y = 0 then i + 1 else r) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hp : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos 64
  by_cases hT : T = 0
  · have hr := h2 hT
    subst hT hr
    by_cases hy0 : y = 0
    · subst hy0; simp [ClzOf]
    · simp only [hy0, and_false, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      refine ⟨by omega, fun h => absurd h hy0, fun _ => ⟨?_, ?_⟩⟩
      · rw [show 64 * (r + 1 - r - 1) = 0 by omega]; omega
      · rw [show 64 * (r + 1 - r) = 64 by omega]; exact hy
  · obtain ⟨lo, hi⟩ := h3 hT
    have hir : 1 ≤ i - r := by
      refine Nat.pos_of_ne_zero fun e => ?_
      rw [e, Nat.mul_zero, Nat.pow_zero] at hi
      omega
    simp only [hT, false_and, ↓reduceIte]
    refine ⟨by omega, fun e => by have := Nat.mul_pos hp (Nat.pos_of_ne_zero hT); omega, fun _ => ⟨?_, ?_⟩⟩
    · rw [show 64 * (i + 1 - r - 1) = 64 + 64 * (i - r - 1) by omega, Nat.pow_add]
      exact Nat.le_trans (Nat.mul_le_mul_left _ lo) (Nat.le_add_left _ _)
    · rw [show 64 * (i + 1 - r) = 64 + 64 * (i - r) by omega, Nat.pow_add]
      calc y + 2 ^ 64 * T < 2 ^ 64 + 2 ^ 64 * T := by omega
        _ = 2 ^ 64 * (T + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        _ ≤ 2 ^ 64 * 2 ^ (64 * (i - r)) := Nat.mul_le_mul_left _ hi

/-- The scan, down the `H` words at `d`: `r10 :=` their leading zero words. -/
theorem clzScan_ok {s : State} {B : Addr} {Z d H : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B (d + 8 * H - 8)) (h8 : s.gpr .r8 = BitVec.ofNat 64 H)
    (h9 : s.gpr .r9 = BitVec.allOnes 64) (h10 : s.gpr .r10 = BitVec.ofNat 64 0)
    (hH : 1 ≤ H) (hH' : H < 2 ^ 32) (hd8 : 8 ≤ d) (hd : d + 8 * H ≤ Z) :
    WP isa (countLoop .r8 clzBody) s fun t =>
      (∃ r, t.gpr .r10 = BitVec.ofNat 64 r ∧ ClzOf (wordsVal s.mem B d H) H r) ∧
      t.mem = s.mem ∧ Keep [.r0, .r3, .r5, .r8, .r9, .r10] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (d + 8 * (H - i) - 8) ∧ t.mem = s.mem ∧
      t.gpr .r9 = (if wordsVal s.mem B (d + 8 * (H - i)) i = 0 then BitVec.allOnes 64 else 0#64) ∧
      (∃ r, t.gpr .r10 = BitVec.ofNat 64 r ∧ ClzOf (wordsVal s.mem B (d + 8 * (H - i)) i) i r) ∧
      Keep [.r0, .r3, .r5, .r8, .r9, .r10] s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := H) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, jm, j9, ⟨r, j10, jc⟩, jk⟩ hc => ?_)
    ⟨by rw [h5, Nat.sub_zero], rfl, by rw [h9]; rfl, ⟨0, h10, by simp [ClzOf, wordsVal]⟩, Keep.refl _ _⟩ h8)
    fun t ⟨_, jm, _, jr, jk⟩ => ⟨by rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at jr; exact jr, jm, jk⟩
  have ek : d + 8 * (H - i) - 8 = d + 8 * (H - 1 - i) := by omega_arith
  rw [ek] at j5
  have hst : WP isa (.block (clzBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (d + 8 * (H - 1 - i)) - BitVec.ofNat 64 8 ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem ∧
        t'.gpr .r9 = t.gpr .r9 &&& ((BitVec.ofNat 64 0 - word t.mem B (d + 8 * (H - 1 - i)) |||
          word t.mem B (d + 8 * (H - 1 - i))) >>> 63 - BitVec.ofNat 64 1) ∧
        t'.gpr .r10 = t.gpr .r10 + (t'.gpr .r9 &&& BitVec.ofNat 64 1)) ∧
      Keep [.r0, .r3, .r5, .r8, .r9, .r10] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j5, (hs.congr jk.wr).ld (show d + 8 * (H - 1 - i) + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l8, lm, l9, l10⟩, lk⟩ => ?_
  rw [jm, zmask] at l9
  generalize hy : word s.mem B (d + 8 * (H - 1 - i)) = y at l9 l10
  have hsucc : wordsVal s.mem B (d + 8 * (H - (i + 1))) (i + 1) =
      y.toNat + 2 ^ 64 * wordsVal s.mem B (d + 8 * (H - i)) i := by
    rw [show d + 8 * (H - (i + 1)) = d + 8 * (H - 1 - i) by omega_arith, wordsVal_succ_low, hy,
      show d + 8 * (H - 1 - i) + 8 = d + 8 * (H - i) by omega_arith]
  have hy0 : y = 0#64 ↔ y.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  have cs := clz_step jc y.isLt
  rw [← hsucc] at cs
  generalize wordsVal s.mem B (d + 8 * (H - i)) i = T at j9 jc cs hsucc
  refine ⟨⟨?_, by rw [lm, jm], ?_, ⟨_, ?_, cs⟩, jk.trans' lk⟩, l8⟩
  · rw [l5, off_sub B (by omega_arith)]; congr 1; omega_arith
  · rw [l9, j9, hsucc]
    by_cases hT : T = 0
    · subst hT
      by_cases hyz : y = 0#64
      · subst hyz; simp
      · simp [hyz, hy0.not.mp hyz]
    · have hne : y.toNat + 2 ^ 64 * T ≠ 0 := fun e => hT (by omega_using [e])
      simp only [hT, hne, ↓reduceIte, BitVec.zero_and]
  · rw [l10, l9, j9, j10]
    by_cases hT : T = 0
    · have hr := jc.2.1 hT
      subst hT hr
      by_cases hyz : y = 0#64
      · subst hyz
        simp only [↓reduceIte, BitVec.and_allOnes]
        (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) <;> omega_arith
      · simp [hyz, hy0.not.mp hyz]
    · simp [hT]

/-- `clzW m sl`, for the narrow `w = 2 H + 2` (`H ≥ 1`): the slot `sl :=` the leading zero words of
`[m]`'s low `H` words. -/
theorem clzW_ok {s : State} {B : Addr} {Z w N m H sl : Nat} (h : Ws s B Z w N) (hm : m < N) (hN : N ≤ 256)
    (hwH : w = 2 * H + 2) (hH : 1 ≤ H) (hsl : sl + 4 ≤ 160) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.clzW m sl) s fun t =>
      ClzOf (wordsVal s.mem B (arr w m) H) H (slot t.mem B sl) ∧
      KeyWorkspace.Keep B w [] [sl] s.mem t.mem ∧ Ws t B Z w N ∧
      Keep [.r0, .r3, .r4, .r5, .r8, .r9, .r10] s t := by
  have := h.wle
  have hnw := h.nowrap
  have hz : 160 ≤ Z := h.hdr_le
  have fm := h.arr_fit hm
  simp only [S] at fm
  have hm8 : 160 ≤ arr w m := Nat.le_add_right VG.Proof.Rsa.KeyWorkspace.hdr (m * S w)
  have e4 : BitVec.ofNat 64 w >>> 1 - BitVec.ofNat 64 1 = BitVec.ofNat 64 H := by
    rw [hwH, show 2 * H + 2 = 2 * (H + 1) by omega, mont_ofNat_shr1 (by omega_arith),
      ofNat_sub' (by omega) (by omega_arith), Nat.add_sub_cancel]
  unfold VG.Impl.Rsa.PPC64LE.RecoverDet.clzW
  simp only [seqs]
  have hb1 : WP isa (.block (ptr .r5 m ++ VG.Impl.Rsa.PPC64LE.RecoverDet.hW ++
      [.lsl .r0 .r4 3, .add .r5 .r5 .r0, .subi .r5 .r5 8, .addi .r8 .r4 0, .li .r9 0,
        .subi .r9 .r9 1, .li .r10 0])) s fun u =>
      (u.gpr .r5 = off B (arr w m + 8 * H - 8) ∧ u.gpr .r8 = BitVec.ofNat 64 H ∧
        u.gpr .r9 = BitVec.allOnes 64 ∧ u.gpr .r10 = BitVec.ofNat 64 0 ∧ u.mem = s.mem) ∧
      Keep [.r0, .r4, .r5, .r8, .r9, .r10] s u := by
    rw [List.append_assoc]
    refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show m < 2 ^ 15 by omega_arith) ?_
    refine WP.mono (WP.keep [.r0, .r4, .r5, .r8, .r9, .r10] (Q := fun u =>
      u.gpr .r5 = off B (arr w m + 8 * H - 8) ∧ u.gpr .r8 = BitVec.ofNat 64 H ∧
      u.gpr .r9 = BitVec.allOnes 64 ∧ u.gpr .r10 = BitVec.ofNat 64 0 ∧ u.mem = s.mem) (by
      prun [VG.Impl.Rsa.PPC64LE.RecoverDet.hW, gpr_write, mem_write, h.r29, e4, shl3_val, off_add,
        off_sub B (show 8 ≤ arr w m + 8 * H by omega_arith)]
      and_intros <;> first | exact BitVec.add_zero _ | decide | rfl) (by decide))
      fun u ⟨q, uk⟩ => ⟨q, ((Keep.write _ .r5 _).trans uk).mono (by decide)⟩
  refine WP.seq (WP.mono hb1 fun s1 ⟨⟨r5, r8, r9, r10, m1⟩, k1⟩ => ?_)
  have hs1 := h.of_keep k1
  refine WP.seq (WP.mono (clzScan_ok (d := arr w m) (H := H) hs1.scr r5 r8 r9 r10 hH (by omega_arith)
    (by omega_arith) (by omega_arith)) fun s2 ⟨⟨r, v10, vc⟩, m2, k2⟩ => ?_)
  have hs2 := hs1.of_keep k2
  rw [m1] at vc
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s2.mem.writeW (off B sl) ((s2.gpr .r10).setWidth 32)) (by
      prun [hs2.r31, hs2.scr.st (show sl + 4 ≤ Z by omega_arith),
        exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sl < 2 ^ 15 by omega_arith)]) (by rfl))
    fun t ⟨mt, kt⟩ => ⟨?_, ?_, hs2.of_keep kt, ((k1.trans k2).trans kt).mono (by decide)⟩
  · have hr : r ≤ H := vc.1
    rw [mt, slot_write_self, BitVec.toNat_setWidth, v10, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega_arith)]
    exact vc
  · rw [mt, m2, m1]; exact keep_slot _ _ (by simp) (by omega_arith)

end ClzW

/-! ## On the arrays of the recovery (`RecDet.DS`) -/

section DSW
open VG.Proof.Bignum.ShiftStages (tz)
open VG.Proof.Rsa.KeyWorkspace (arr S num)
open VG.Proof.Rsa.PPC64LE.RecDet (DS upd updV Sep vw vN vw_wide vw_false vN_le)
open VG.Proof.Rsa.PPC64LE.Recover (rvB kK ww)

variable {s0 s : State} {A : Bool → Nat → Nat} {live : List (Bool × Nat)} {V : Nat → Nat} {ls : List Nat}

/-- An array of `w = 2 L` words of 32 bits as `L` of 64. -/
theorem num_words (m : Mem) (B : Addr) {w L : Nat} (j : Nat) (hw : w = 2 * L) :
    num m B w j = wordsVal m B (arr w j) L := by
  rw [wordsVal_eq_val32, ← hw]

/-- The low `H` words of `w = 2 H + 2` words of 32 bits. -/
theorem num_low (m : Mem) (B : Addr) {w H : Nat} (j : Nat) (hw : w = 2 * H + 2) :
    wordsVal m B (arr w j) H = num m B w j % 2 ^ (64 * H) := by
  show _ = val32 _ _ _ _ % _
  rw [wordsVal_eq_val32, hw, val32_append, show 32 * (2 * H) = 64 * H by omega, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by rw [← show 32 * (2 * H) = 64 * H by omega]; exact val32_lt _ _ _ _)]

theorem wide_L (s0 : State) : vw s0 true = 2 * (vw s0 false + 1) := by rw [vw_wide]; omega

/-- `tzW` on the wide view: two slots, the trailing zeros of `[a] ∨ [b]` in words and bits. -/
theorem DS.tzWW (h : DS s0 true A live V ls s) {a b sw sb : Nat} (ha : (true, a) ∈ live) (hb : (true, b) ∈ live)
    (hsw : sw + 4 ≤ 160) (hsb : sb + 4 ≤ 160) (hss : sw + 4 ≤ sb) (hY : A true a ||| A true b ≠ 0)
    {ls' : List Nat} (hl : ∀ e ∈ ls', e ∈ ls ∧ (e + 4 ≤ sw ∨ sw + 4 ≤ e) ∧ (e + 4 ≤ sb ∨ sb + 4 ≤ e)) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.tzW a b sw sb) s fun t =>
      DS s0 true A live (updV (updV V sw (tz (A true a ||| A true b) / 64)) sb (tz (A true a ||| A true b) % 64))
        (sb :: sw :: ls') t ∧ Keep shRegs s t := by
  have w1 := h.base.sz.w1
  have hL := wide_L s0
  have ea : wordsVal s.mem (rvB s0) (arr (vw s0 true) a) (vw s0 false + 1) = A true a := by
    rw [← num_words _ _ _ hL]; exact h.val ha
  have eb : wordsVal s.mem (rvB s0) (arr (vw s0 true) b) (vw s0 false + 1) = A true b := by
    rw [← num_words _ _ _ hL]; exact h.val hb
  refine WP.mono (tzW_ok h.ws (h.live_lt _ ha) (h.live_lt _ hb) (vN_le true) hL (by omega) hsw hsb (.inl hss)
    (by rw [ea, eb]; exact hY)) fun t ⟨v1, v2, k, wt, kt⟩ => ⟨?_, kt⟩
  rw [ea, eb] at v1 v2
  exact h.wrS2 wt hsw hsb hss k v1 v2 hl kt

/-- `shrBy` on the wide view: `[j] := ⌊[j] / 2^(64 c_w + c_b)⌋`, the counts in the slots. -/
theorem DS.shrByW (h : DS s0 true A live V ls s) {j sw sb : Nat} (hj : (true, j) ∈ live) (hsw : sw ∈ ls)
    (hsb : sb ∈ ls) (cwL : V sw < vw s0 false + 1) (cb64 : V sb < 64) {live' : List (Bool × Nat)}
    (hl : ∀ e ∈ live', e ∈ live ∧ Sep (true, j) e) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shrBy j sw sb) s fun t =>
      DS s0 true (upd A true j (A true j / 2 ^ (64 * V sw + V sb))) ((true, j) :: live') V ls t ∧
        Keep shRegs s t := by
  have w1 := h.base.sz.w1
  have hL := wide_L s0
  have ej : wordsVal s.mem (rvB s0) (arr (vw s0 true) j) (vw s0 false + 1) = A true j := by
    rw [← num_words _ _ _ hL]; exact h.val hj
  refine WP.mono (shrBy_ok h.ws (h.live_lt _ hj) (vN_le true) hL (by rw [vw_false]; omega) (h.ls_ok _ hsw)
    (h.ls_ok _ hsb) (h.sl _ hsw) (h.sl _ hsb) cwL cb64) fun t ⟨v, o, wt, kt⟩ => ⟨?_, kt⟩
  have hS : 0 + 8 * (vw s0 false + 1) ≤ S (vw s0 true) := by rw [hL]; simp only [S]; omega
  have k : KeyWorkspace.Keep (rvB s0) (vw s0 true) [j] [] s.mem t.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa using o) hS (by simp)
  refine h.wr wt (h.live_lt _ hj) k ?_ hl kt
  rw [num_words _ _ _ hL, v, ej]

/-- `shlBy` on the wide view: `[j] := [j] 2^(64 c_w + c_b) mod 2^(32 W)` (without `c_b` unless
`bits`), the counts in the slots. -/
theorem DS.shlByW (bits : Bool) (h : DS s0 true A live V ls s) {j sw sb : Nat} (hj : (true, j) ∈ live)
    (hsw : sw ∈ ls) (hsb : sb ∈ ls) (cwL : V sw < vw s0 false + 1) (cb64 : bits = true → V sb < 64)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (true, j) e) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shlBy j sw sb bits) s fun t =>
      DS s0 true (upd A true j (A true j * 2 ^ (64 * V sw + (if bits then V sb else 0)) % 2 ^ (32 * vw s0 true)))
        ((true, j) :: live') V ls t ∧ Keep shRegs s t := by
  have w1 := h.base.sz.w1
  have hL := wide_L s0
  have ej : wordsVal s.mem (rvB s0) (arr (vw s0 true) j) (vw s0 false + 1) = A true j := by
    rw [← num_words _ _ _ hL]; exact h.val hj
  refine WP.mono (shlBy_ok bits h.ws (h.live_lt _ hj) (vN_le true) hL (by rw [vw_false]; omega) (h.ls_ok _ hsw)
    (h.ls_ok _ hsb) (h.sl _ hsw) (h.sl _ hsb) cwL cb64) fun t ⟨v, o, wt, kt⟩ => ⟨?_, kt⟩
  have hS : 0 + 8 * (vw s0 false + 1) ≤ S (vw s0 true) := by rw [hL]; simp only [S]; omega
  have k : KeyWorkspace.Keep (rvB s0) (vw s0 true) [j] [] s.mem t.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa using o) hS (by simp)
  refine h.wr wt (h.live_lt _ hj) k ?_ hl kt
  rw [num_words _ _ _ hL, v, ej, show 64 * (vw s0 false + 1) = 32 * vw s0 true by rw [hL]; omega]

/-- `clzW` on the narrow view: a slot, the leading zero words of `[m]`'s low `h = ⌈k / 8⌉` words. -/
theorem DS.clzWN (h : DS s0 false A live V ls s) {m sl : Nat} (hm : (false, m) ∈ live) (hsl : sl + 4 ≤ 160)
    {ls' : List Nat} (hl : ∀ e ∈ ls', e ∈ ls ∧ (e + 4 ≤ sl ∨ sl + 4 ≤ e)) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.clzW m sl) s fun t => ∃ c,
      ClzOf (A false m % 2 ^ (64 * ((kK s0 + 7) / 8))) ((kK s0 + 7) / 8) c ∧
      DS s0 false A live (updV V sl c) (sl :: ls') t ∧ Keep [.r0, .r3, .r4, .r5, .r8, .r9, .r10] s t := by
  have w1 := h.base.sz.w1
  have hw : vw s0 false = 2 * ((kK s0 + 7) / 8) + 2 := by rw [vw_false]
  refine WP.mono (clzW_ok h.ws (h.live_lt _ hm) (vN_le false) hw (by simp only [ww] at w1; omega) hsl) fun t ⟨c, k, wt, kt⟩ =>
    ⟨_, ?_, h.wrS wt hsl k rfl hl kt, kt⟩
  rw [num_low _ _ _ hw, h.val hm] at c
  exact c

end DSW

end VG.Proof.Rsa.PPC64LE.RdShift
