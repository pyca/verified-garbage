module

public import VerifiedGarbage.Impl.Rsa.RISCV64.Div
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public import VerifiedGarbage.Proof.Rsa.KeyMath
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The division of the RSA key operations on RISC-V

In words of 64 bits, against `Div.div`'s non-restoring steps:

* `passLoop_ok`: a pass over the remainder's words one at a time,
  `2 [r] + c + ([d] ⊕ mask)` with its carries; `pass4Loop_ok`: four at a
  time (`passAt_ok` a word at an offset, `PassDone` what a pass has done to
  its first words); `passes_ok`: a step's pass, `(k + 1) mod 4` words one at
  a time, then the others four at a time. `fixLoop_ok`: the final
  `[r] + ([d] ∧ mask)`.
* `qv`: the words of `[q]` after some of the quotient's bits, the dividend's
  bits not yet taken below them in the same word.
* `step_run`: a step, run; `step_ok`: it keeps `DivInv` one bit further, the
  remainder `R` and quotient `Q` of the dividend's bits taken (`R < D`), with
  `[r]` holding `R` or `R - D` (mod `2^(64 (w + 1))`) as the mask says.
* `div_ok`: the `64 w` steps from `(0, 0)` and the correction, the
  quotient `N / D` and the remainder `N mod D` when `D > 0`; for `D = 0` it
  runs all the same.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Loops
  VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr ptrs subN selBody mov)
open VG.Impl.Rsa.RISCV64.Div (shlBody qword passBody fixBody fixK stepK divK init div wordsOf divL passes)

/-- The `w + 1` words of array `j` (the remainder of the division). -/
abbrev num1 (m : Mem) (B : Addr) (w j : Nat) : Nat := wordsVal m B (arr w j) (w + 1)

/-- The `k + 1` words of array `j` (the remainder of the division with `k` words). -/
abbrev numk (m : Mem) (B : Addr) (w j k : Nat) : Nat := wordsVal m B (arr w j) (k + 1)

/-- The registers the division may change. -/
abbrev divRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a5, .s7]

/-- `w` words and one more. -/
theorem num1_eq (m : Mem) (B : Addr) (w j : Nat) :
    num1 m B w j = num m B w j + 2 ^ (64 * w) * (word m B (arr w j + 8 * w)).toNat :=
  wordsVal_succ_top _ _ _ _

/-- The `w + 1` words of an array outside the frame. -/
theorem Frame.num1 {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 8 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) : num1 m' B w j = num1 m B w j := by
  have hS : S w = 8 * (w + 2) := rfl
  exact h.words (fun k hk => by have := arr_disj (w := w) (hj k hk); omega_arith)
    (fun d hd' => by have := hd d hd'; have := hdr_le_arr w j; omega_arith) (by omega_arith)

/-! ## The left shift -/

/-- A word of the left shift: `2 x + c` split into its low word and the carry out. -/
theorem shl64_arith (x c : BitVec 64) (hc : c.toNat ≤ 1) :
    (x <<< 1 ||| c).toNat + 2 ^ 64 * (x >>> 63).toNat = 2 * x.toNat + c.toNat ∧ (x >>> 63).toNat ≤ 1 := by
  have hx := x.isLt
  have h1 : (x <<< 1).toNat = 2 * x.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega_arith
  have h2 : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd : x <<< 1 &&& c = 0 := by
    rcases (show c.toNat = 0 ∨ c.toNat = 1 by omega_arith) with z | z
    · rw [show c = 0#64 from BitVec.eq_of_toNat_eq z, BitVec.and_zero]; rfl
    · rw [show c = 1#64 from BitVec.eq_of_toNat_eq z]
      apply BitVec.eq_of_getElem_eq; intro i hi
      simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
      by_cases h : i = 0
      · subst h; simp
      · simp [h]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
  have := Nat.div_add_mod x.toNat (2 ^ 63)
  have := Nat.mod_lt x.toNat (show 0 < 2 ^ 63 by decide)
  constructor <;> omega_arith

/-- The left shift of `n` words at `t0` (`countLoop .t3 shlBody`), the carry in
and out in `t4`. -/
theorem shlLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h4 : (s.gpr .t4).toNat ≤ 1)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO8 : dO % 8 = 0) (hO : dO + 8 * n ≤ Z) :
    WP isa (countLoop .t3 shlBody) s fun t =>
      (t.gpr .t4).toNat ≤ 1 ∧
      wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .t4).toNat = 2 * wordsVal s.mem B dO n + (s.gpr .t4).toNat ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ (t.gpr .t4).toNat ≤ 1 ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .t4).toNat = 2 * wordsVal s.mem B dO i + (s.gpr .t4).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (shlBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j4, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, h4, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, j4, jout, jeq, jk⟩ => ⟨j4, jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (shlBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) (word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t4) ∧
        t'.gpr .t4 = word t.mem B (dO + 8 * i) >>> 63) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [shlBody, j0, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l3, lm, l4⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l4]; exact (shl64_arith _ _ j4).2
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have k := (shl64_arith (word s.mem B (dO + 8 * i)) (t.gpr .t4) j4).1
    rw [lm, l4, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wa, wordsVal_succ_top s.mem B dO i,
      Nat.mul_succ, Nat.pow_add]
    have e : 2 ^ (64 * i) * (word s.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t4).toNat +
        2 ^ (64 * i) * 2 ^ 64 * (word s.mem B (dO + 8 * i) >>> 63).toNat =
        2 * (2 ^ (64 * i) * (word s.mem B (dO + 8 * i)).toNat) + 2 ^ (64 * i) * (t.gpr .t4).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, k, Nat.mul_add, Nat.mul_left_comm]
    grind

/-! ## The words of a step -/

/-- Two additions and their carries, never both set: `x + c + y`. -/
theorem adc64_arith (x c y : BitVec 64) (hc : c.toNat ≤ 1) :
    (x + c + y).toNat + 2 ^ 64 * ((if x + c + y < y then (1 : BitVec 64) else 0) |||
        (if x + c < c then 1 else 0)).toNat = x.toNat + c.toNat + y.toNat ∧
      ((if x + c + y < y then (1 : BitVec 64) else 0) ||| (if x + c < c then 1 else 0)).toNat ≤ 1 := by
  have hx := x.isLt
  have hy := y.isLt
  have A : (x + c).toNat = (x.toNat + c.toNat) % 2 ^ 64 := BitVec.toNat_add x c
  have Bq : (x + c + y).toNat = ((x + c).toNat + y.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have o00 : ((0 : BitVec 64) ||| 0).toNat = 0 := by decide
  have o01 : ((0 : BitVec 64) ||| 1).toNat = 1 := by decide
  have o10 : ((1 : BitVec 64) ||| 0).toNat = 1 := by decide
  have o11 : ((1 : BitVec 64) ||| 1).toNat = 1 := by decide
  by_cases h1 : x + c < c <;> by_cases h2 : x + c + y < y <;>
    simp only [h1, h2, ite_true, ite_false, o00, o01, o10, o11] <;>
    rw [BitVec.lt_def] at h1 h2 <;> omega

/-- A mask of `b`. -/
abbrev dmask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem xor_mask_toNat (y : BitVec 64) (b : Bool) :
    (y ^^^ dmask b).toNat + (if b then y.toNat else 0) = if b then 2 ^ 64 - 1 else y.toNat := by
  have := y.isLt
  cases b
  · show (y ^^^ 0#64).toNat + 0 = y.toNat; rw [BitVec.xor_zero]; rfl
  · show (y ^^^ BitVec.allOnes 64).toNat + y.toNat = 2 ^ 64 - 1
    rw [BitVec.xor_allOnes, BitVec.toNat_not]; omega

theorem and_mask_eq (y : BitVec 64) (b : Bool) : y &&& dmask b = if b then y else 0 := by
  cases b
  · show y &&& 0#64 = 0; exact BitVec.and_zero
  · show y &&& BitVec.allOnes 64 = y; exact BitVec.and_allOnes

/-- The registers a pass changes. -/
abbrev passRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a5]

/-- A word of a pass: `2 x + c₃ + c₄ + (y ⊕ mask)`. -/
theorem pass64_arith (x y c3 c4 : BitVec 64) (b : Bool) (h3 : c3.toNat ≤ 1) (h4 : c4.toNat ≤ 1) :
    let sh := x <<< 1 ||| c3
    let c' := (if sh + c4 + (y ^^^ dmask b) < y ^^^ dmask b then (1 : BitVec 64) else 0) |||
      (if sh + c4 < c4 then 1 else 0)
    (sh + c4 + (y ^^^ dmask b)).toNat + 2 ^ 64 * ((x >>> 63).toNat + c'.toNat) + (if b then y.toNat else 0) =
        2 * x.toNat + c3.toNat + c4.toNat + (if b then 2 ^ 64 - 1 else y.toNat) ∧
      (x >>> 63).toNat ≤ 1 ∧ c'.toNat ≤ 1 := by
  intro sh c'
  obtain ⟨e1, l1⟩ := shl64_arith x c3 h3
  obtain ⟨e2, l2⟩ := adc64_arith sh c4 (y ^^^ dmask b) h4
  have e3 := xor_mask_toNat y b
  refine ⟨?_, l1, l2⟩
  rw [Nat.mul_add]
  change (sh + c4 + (y ^^^ dmask b)).toNat + 2 ^ 64 * c'.toNat = _ at e2
  change sh.toNat + _ = _ at e1
  omega

/-- `[o] := 2 [o] + c₃ + c₄ + ([d] ⊕ mask)` over `n` words (`countLoop .t2 passBody`): the
shift's carry in and out in `t3`, the addition's in `t4`, the last word in `t6`. -/
theorem passLoop_ok {s : State} {B : Addr} {Z dO dB n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dB) (h2 : s.gpr .t2 = BitVec.ofNat 64 n)
    (h3 : (s.gpr .t3).toNat ≤ 1) (h4 : (s.gpr .t4).toNat ≤ 1) (ha : s.gpr .a4 = dmask b)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO8 : dO % 8 = 0) (hB8 : dB % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hB : dB + 8 * n ≤ Z) (dOB : dO + 8 * n ≤ dB ∨ dB + 8 * n ≤ dO) :
    WP isa (countLoop .t2 passBody) s fun t =>
      t.gpr .t0 = off B (dO + 8 * n) ∧ t.gpr .t1 = off B (dB + 8 * n) ∧
      (t.gpr .t3).toNat ≤ 1 ∧ (t.gpr .t4).toNat ≤ 1 ∧ t.gpr .t6 = word t.mem B (dO + 8 * (n - 1)) ∧
      wordsVal t.mem B dO n + 2 ^ (64 * n) * ((t.gpr .t3).toNat + (t.gpr .t4).toNat) +
          (if b then wordsVal s.mem B dB n + 1 else 0) =
        2 * wordsVal s.mem B dO n + (s.gpr .t3).toNat + (s.gpr .t4).toNat +
          (if b then 2 ^ (64 * n) else wordsVal s.mem B dB n) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep passRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dB + 8 * i) ∧
      (t.gpr .t3).toNat ≤ 1 ∧ (t.gpr .t4).toNat ≤ 1 ∧
      (0 < i → t.gpr .t6 = word t.mem B (dO + 8 * (i - 1))) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * ((t.gpr .t3).toNat + (t.gpr .t4).toNat) +
          (if b then wordsVal s.mem B dB i + 1 else 0) =
        2 * wordsVal s.mem B dO i + (s.gpr .t3).toNat + (s.gpr .t4).toNat +
          (if b then 2 ^ (64 * i) else wordsVal s.mem B dB i) ∧
      Keep passRegs s t
  refine WP.mono (wp_countdown (body := .block (passBody ++ ([.addi .t2 .t2 (-1)] : List Instr)))
    (cnt := .t2) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j3, j4, j6, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, h3, h4, fun h => absurd h (Nat.lt_irrefl 0), Outside.refl _ _ _ _,
      by cases b <;> simp [wordsVal], Keep.refl _ _⟩ h2)
    fun t ⟨j0, j1, j3, j4, j6, jout, jeq, jk⟩ => ⟨j0, j1, j3, j4, j6 (by omega_arith), jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .a4 = dmask b := (jk.gpr (r := .a4) (by decide)).trans ha
  have hst : WP isa (.block (passBody ++ ([.addi .t2 .t2 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dB + 8 * i + 8) ∧
        t'.gpr .t2 = t.gpr .t2 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          ((word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t3) + t.gpr .t4 + (word t.mem B (dB + 8 * i) ^^^ dmask b)) ∧
        t'.gpr .t6 = (word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t3) + t.gpr .t4 +
          (word t.mem B (dB + 8 * i) ^^^ dmask b) ∧
        t'.gpr .t3 = word t.mem B (dO + 8 * i) >>> 63 ∧
        t'.gpr .t4 = ((if (word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t3) + t.gpr .t4 +
              (word t.mem B (dB + 8 * i) ^^^ dmask b) < word t.mem B (dB + 8 * i) ^^^ dmask b
            then (1 : BitVec 64) else 0) |||
          (if (word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t3) + t.gpr .t4 < t.gpr .t4 then 1 else 0))) ∧
      Keep passRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [passBody, j0, j1, ja, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dB + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dB + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, lm, l6, l3, l4⟩, lk⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l2⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · rw [l3]; exact (pass64_arith _ (word t.mem B (dB + 8 * i)) _ _ b j3 j4).2.1
  · rw [l4]; exact (pass64_arith _ _ _ _ b j3 j4).2.2
  · intro _; rw [l6, lm, Nat.add_sub_cancel, word_writeW_self]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wb : word t.mem B (dB + 8 * i) = word s.mem B (dB + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have k := (pass64_arith (word t.mem B (dO + 8 * i)) (word t.mem B (dB + 8 * i)) (t.gpr .t3) (t.gpr .t4)
      b j3 j4).1
    rw [← l3, ← l4, wa, wb] at k
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dB i,
      wordsVal_succ_top s.mem B dO i, Nat.mul_succ, Nat.pow_add, wa, wb]
    generalize (word s.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t3) + t.gpr .t4 +
      (word s.mem B (dB + 8 * i) ^^^ dmask b) = o at k ⊢
    generalize 2 ^ (64 * i) = P at jeq ⊢
    cases b
    · simp only [Bool.false_eq_true, ite_false] at k jeq ⊢
      grind
    · simp only [ite_true] at k jeq ⊢
      grind

/-! ## The pass four words at a time -/

/-- What a pass has done to its first `i` words, from `s`: the carries bits, the
last word written in `t6`, nothing but those words written, and the value. -/
def PassDone (s t : State) (B : Addr) (dO dB : Nat) (b : Bool) (i : Nat) : Prop :=
  (t.gpr .t3).toNat ≤ 1 ∧ (t.gpr .t4).toNat ≤ 1 ∧
    (0 < i → t.gpr .t6 = word t.mem B (dO + 8 * (i - 1))) ∧ Outside B dO (8 * i) s.mem t.mem ∧
    wordsVal t.mem B dO i + 2 ^ (64 * i) * ((t.gpr .t3).toNat + (t.gpr .t4).toNat) +
        (if b then wordsVal s.mem B dB i + 1 else 0) =
      2 * wordsVal s.mem B dO i + (s.gpr .t3).toNat + (s.gpr .t4).toNat +
        (if b then 2 ^ (64 * i) else wordsVal s.mem B dB i)

theorem PassDone.zero {s : State} {B : Addr} {dO dB : Nat} {b : Bool}
    (h3 : (s.gpr .t3).toNat ≤ 1) (h4 : (s.gpr .t4).toNat ≤ 1) : PassDone s s B dO dB b 0 :=
  ⟨h3, h4, fun h => absurd h (Nat.lt_irrefl 0), Outside.refl _ _ _ _, by cases b <;> simp [wordsVal]⟩

/-- The value a pass writes to its word at `dO + 8 i`. -/
abbrev passV (t : State) (B : Addr) (dO dB : Nat) (b : Bool) (i : Nat) : BitVec 64 :=
  (word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t3) + t.gpr .t4 + (word t.mem B (dB + 8 * i) ^^^ dmask b)

/-- The addition's carry out of that word. -/
abbrev passC (t : State) (B : Addr) (dO dB : Nat) (b : Bool) (i : Nat) : BitVec 64 :=
  (if passV t B dO dB b i < word t.mem B (dB + 8 * i) ^^^ dmask b then (1 : BitVec 64) else 0) |||
    (if (word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t3) + t.gpr .t4 < t.gpr .t4 then 1 else 0)

/-- One more word of a pass. -/
theorem PassDone.step {s t t' : State} {B : Addr} {Z dO dB : Nat} {b : Bool} {i : Nat}
    (hs : Scr s B Z) (hd : PassDone s t B dO dB b i)
    (hO : dO + 8 * (i + 1) ≤ Z) (hB : dB + 8 * (i + 1) ≤ Z)
    (dOB : dO + 8 * (i + 1) ≤ dB ∨ dB + 8 * (i + 1) ≤ dO)
    (hm : t'.mem = t.mem.writeW (off B (dO + 8 * i)) (passV t B dO dB b i))
    (h6 : t'.gpr .t6 = passV t B dO dB b i) (h3 : t'.gpr .t3 = word t.mem B (dO + 8 * i) >>> 63)
    (h4 : t'.gpr .t4 = passC t B dO dB b i) : PassDone s t' B dO dB b (i + 1) := by
  have hnw := hs.nowrap
  obtain ⟨j3, j4, _, jout, jeq⟩ := hd
  dsimp only [passV, passC] at hm h6 h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h3]; exact (pass64_arith _ (word t.mem B (dB + 8 * i)) _ _ b j3 j4).2.1
  · rw [h4]; exact (pass64_arith _ _ _ _ b j3 j4).2.2
  · intro _; rw [h6, hm, Nat.add_sub_cancel, word_writeW_self]
  · rw [hm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wb : word t.mem B (dB + 8 * i) = word s.mem B (dB + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have k := (pass64_arith (word t.mem B (dO + 8 * i)) (word t.mem B (dB + 8 * i)) (t.gpr .t3) (t.gpr .t4)
      b j3 j4).1
    rw [← h3, ← h4, wa, wb] at k
    rw [hm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dB i,
      wordsVal_succ_top s.mem B dO i, Nat.mul_succ, Nat.pow_add, wa, wb]
    generalize (word s.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t3) + t.gpr .t4 +
      (word s.mem B (dB + 8 * i) ^^^ dmask b) = o at k ⊢
    generalize 2 ^ (64 * i) = P at jeq ⊢
    cases b
    · simp only [Bool.false_eq_true, ite_false] at k jeq ⊢
      grind
    · simp only [ite_true] at k jeq ⊢
      grind

theorem passAt_writes (o : Nat) :
    writesOnly [.t3, .t4, .t5, .t6, .a5] (.block (VG.Impl.Rsa.RISCV64.Div.passAt o)) = true := by
  rfl

/-- `passAt o`: the pass's word at `dO + 8 i`, the pointers `o` before it. -/
theorem passAt_ok {t : State} {B : Addr} {Z dO dB : Nat} (ht : Scr t B Z) {b : Bool} {i o : Nat}
    (h0 : t.gpr .t0 = off B (dO + 8 * i - o)) (h1 : t.gpr .t1 = off B (dB + 8 * i - o))
    (ha : t.gpr .a4 = dmask b) (ho : o < 2048) (hoi : o ≤ 8 * i) (hO8 : dO % 8 = 0) (hB8 : dB % 8 = 0)
    (hO : dO + 8 * i + 8 ≤ Z) (hB : dB + 8 * i + 8 ≤ Z) :
    WP isa (.block (VG.Impl.Rsa.RISCV64.Div.passAt o)) t fun t' =>
      (t'.mem = t.mem.writeW (off B (dO + 8 * i)) (passV t B dO dB b i) ∧
        t'.gpr .t6 = passV t B dO dB b i ∧ t'.gpr .t3 = word t.mem B (dO + 8 * i) >>> 63 ∧
        t'.gpr .t4 = passC t B dO dB b i) ∧ Keep [.t3, .t4, .t5, .t6, .a5] t t' := by
  refine WP.keep _ ?_ (passAt_writes o) (by rfl)
  have e0 : dO + 8 * i - o + o = dO + 8 * i := by omega_arith
  have e1 : dB + 8 * i - o + o = dB + 8 * i := by omega_arith
  unfold VG.Impl.Rsa.RISCV64.Div.passAt
  brun [h0, h1, ha, ho, e0, e1, ht.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
    ht.ld (show dB + 8 * i + 8 ≤ Z by omega_arith), ht.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
    ht.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
    ht.al8 (show dB + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]

theorem PassDone.congr {s t t' : State} {B : Addr} {dO dB : Nat} {b : Bool} {i : Nat}
    (hd : PassDone s t B dO dB b i) (hm : t'.mem = t.mem) (h3 : t'.gpr .t3 = t.gpr .t3)
    (h4 : t'.gpr .t4 = t.gpr .t4) (h6 : t'.gpr .t6 = t.gpr .t6) : PassDone s t' B dO dB b i := by
  obtain ⟨j3, j4, j6, jo, je⟩ := hd
  exact ⟨h3 ▸ j3, h4 ▸ j4, fun h => by rw [h6, hm]; exact j6 h, hm ▸ jo, by rw [hm, h3, h4]; exact je⟩

theorem rem4_ofNat (n : Nat) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 3 = BitVec.ofNat 64 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  have a := Nat.and_two_pow_sub_one_eq_mod n 2
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod] at a ⊢
  rw [Nat.mod_eq_of_lt h, a]
  omega_arith

theorem quot4_ofNat (n : Nat) (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 2 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- `g` times four words of a pass (`countLoop .t2 pass4`), after its first `r` words. -/
theorem pass4Loop_ok {s t : State} {B : Addr} {Z dO dB r g : Nat} (hs : Scr s B Z) {b : Bool}
    (hd : PassDone s t B dO dB b r) (hwr : t.wr = s.wr)
    (h0 : t.gpr .t0 = off B (dO + 8 * r)) (h1 : t.gpr .t1 = off B (dB + 8 * r))
    (h2 : t.gpr .t2 = BitVec.ofNat 64 g) (ha : t.gpr .a4 = dmask b)
    (hg : 1 ≤ g) (hg' : g < 2 ^ 32) (hO8 : dO % 8 = 0) (hB8 : dB % 8 = 0)
    (hO : dO + 8 * (r + 4 * g) ≤ Z) (hB : dB + 8 * (r + 4 * g) ≤ Z)
    (dOB : dO + 8 * (r + 4 * g) ≤ dB ∨ dB + 8 * (r + 4 * g) ≤ dO) :
    WP isa (countLoop .t2 VG.Impl.Rsa.RISCV64.Div.pass4) t fun u =>
      PassDone s u B dO dB b (r + 4 * g) ∧ Keep passRegs t u := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i u =>
    u.gpr .t0 = off B (dO + 8 * (r + 4 * i)) ∧ u.gpr .t1 = off B (dB + 8 * (r + 4 * i)) ∧
      PassDone s u B dO dB b (r + 4 * i) ∧ Keep passRegs t u
  refine WP.mono (wp_countdown
    (body := .block (VG.Impl.Rsa.RISCV64.Div.pass4 ++ ([.addi .t2 .t2 (-1)] : List Instr)))
    (cnt := .t2) (N := g) (by omega_arith) (by omega_arith) Inv
    (fun i hi u ⟨u0, u1, ud, uk⟩ _ => ?_)
    ⟨by rw [h0, Nat.mul_zero, Nat.add_zero], by rw [h1, Nat.mul_zero, Nat.add_zero],
      by rw [Nat.mul_zero, Nat.add_zero]; exact hd, Keep.refl _ _⟩ h2)
    fun u ⟨_, _, ud, uk⟩ => ⟨ud, uk⟩
  have hsu : Scr u B Z := hs.congr (uk.2.2.trans hwr)
  have ua : u.gpr .a4 = dmask b := (uk.gpr (r := .a4) (by decide)).trans ha
  obtain ⟨c, hc⟩ : ∃ c, r + 4 * i = c := ⟨_, rfl⟩
  rw [hc] at u0 u1 ud
  have hc4 : r + 4 * (i + 1) = c + 1 + 1 + 1 + 1 := by omega_arith
  simp only [VG.Impl.Rsa.RISCV64.Div.pass4, List.append_assoc]
  -- The four words.
  rw [WP.block_append_iff]
  refine WP.mono (passAt_ok hsu (b := b) (i := c) (o := 0) (by rw [u0, Nat.sub_zero])
    (by rw [u1, Nat.sub_zero]) ua (by decide) (by omega_arith) hO8 hB8 (by omega_arith) (by omega_arith))
    fun v1 ⟨⟨m1, e6, e3, e4⟩, k1⟩ => ?_
  have d1 := PassDone.step hs ud (by omega_arith) (by omega_arith) (by omega_arith) m1 e6 e3 e4
  have s1 : Scr v1 B Z := hsu.congr k1.2.2
  have p0 : v1.gpr .t0 = off B (dO + 8 * c) := (k1.gpr (r := .t0) (by decide)).trans u0
  have p1 : v1.gpr .t1 = off B (dB + 8 * c) := (k1.gpr (r := .t1) (by decide)).trans u1
  have a1 : v1.gpr .a4 = dmask b := (k1.gpr (r := .a4) (by decide)).trans ua
  rw [WP.block_append_iff]
  refine WP.mono (passAt_ok s1 (b := b) (i := c + 1) (o := 8)
    (by rw [p0, show dO + 8 * (c + 1) - 8 = dO + 8 * c by omega_arith])
    (by rw [p1, show dB + 8 * (c + 1) - 8 = dB + 8 * c by omega_arith]) a1 (by decide) (by omega_arith)
    hO8 hB8 (by omega_arith) (by omega_arith))
    fun v2 ⟨⟨m2, f6, f3, f4⟩, k2⟩ => ?_
  have d2 := PassDone.step hs d1 (by omega_arith) (by omega_arith) (by omega_arith) m2 f6 f3 f4
  have s2 : Scr v2 B Z := s1.congr k2.2.2
  have q0 : v2.gpr .t0 = off B (dO + 8 * c) := (k2.gpr (r := .t0) (by decide)).trans p0
  have q1 : v2.gpr .t1 = off B (dB + 8 * c) := (k2.gpr (r := .t1) (by decide)).trans p1
  have a2 : v2.gpr .a4 = dmask b := (k2.gpr (r := .a4) (by decide)).trans a1
  rw [WP.block_append_iff]
  refine WP.mono (passAt_ok s2 (b := b) (i := c + 1 + 1) (o := 16)
    (by rw [q0, show dO + 8 * (c + 1 + 1) - 16 = dO + 8 * c by omega_arith])
    (by rw [q1, show dB + 8 * (c + 1 + 1) - 16 = dB + 8 * c by omega_arith]) a2 (by decide) (by omega_arith)
    hO8 hB8 (by omega_arith) (by omega_arith))
    fun v3 ⟨⟨m3, g6, g3, g4⟩, k3⟩ => ?_
  have d3 := PassDone.step hs d2 (by omega_arith) (by omega_arith) (by omega_arith) m3 g6 g3 g4
  have s3 : Scr v3 B Z := s2.congr k3.2.2
  have r0 : v3.gpr .t0 = off B (dO + 8 * c) := (k3.gpr (r := .t0) (by decide)).trans q0
  have r1 : v3.gpr .t1 = off B (dB + 8 * c) := (k3.gpr (r := .t1) (by decide)).trans q1
  have a3 : v3.gpr .a4 = dmask b := (k3.gpr (r := .a4) (by decide)).trans a2
  rw [WP.block_append_iff]
  refine WP.mono (passAt_ok s3 (b := b) (i := c + 1 + 1 + 1) (o := 24)
    (by rw [r0, show dO + 8 * (c + 1 + 1 + 1) - 24 = dO + 8 * c by omega_arith])
    (by rw [r1, show dB + 8 * (c + 1 + 1 + 1) - 24 = dB + 8 * c by omega_arith]) a3 (by decide)
    (by omega_arith) hO8 hB8 (by omega_arith) (by omega_arith))
    fun v4 ⟨⟨m4, h6, h3, h4⟩, k4⟩ => ?_
  have d4 := PassDone.step hs d3 (by omega_arith) (by omega_arith) (by omega_arith) m4 h6 h3 h4
  have w0 : v4.gpr .t0 = off B (dO + 8 * c) := (k4.gpr (r := .t0) (by decide)).trans r0
  have w1 : v4.gpr .t1 = off B (dB + 8 * c) := (k4.gpr (r := .t1) (by decide)).trans r1
  have w2 : v4.gpr .t2 = u.gpr .t2 :=
    (k4.gpr (r := .t2) (by decide)).trans ((k3.gpr (r := .t2) (by decide)).trans
      ((k2.gpr (r := .t2) (by decide)).trans (k1.gpr (r := .t2) (by decide))))
  -- The pointers and the count.
  have hb : WP isa (.block ([.addi .t0 .t0 32, .addi .t1 .t1 32] ++ ([.addi .t2 .t2 (-1)] : List Instr))) v4
      fun x => (x.gpr .t0 = off B (dO + 8 * c + 32) ∧ x.gpr .t1 = off B (dB + 8 * c + 32) ∧
        x.gpr .t2 = v4.gpr .t2 - BitVec.ofNat 64 1 ∧ x.mem = v4.mem) ∧ Keep [.t0, .t1, .t2] v4 x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [w0, w1]
  refine WP.mono hb fun x ⟨⟨x0, x1, x2, xm⟩, kx⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, by rw [x2, w2]⟩
  · rw [x0, hc4, show dO + 8 * c + 32 = dO + 8 * (c + 1 + 1 + 1 + 1) by omega_arith]
  · rw [x1, hc4, show dB + 8 * c + 32 = dB + 8 * (c + 1 + 1 + 1 + 1) by omega_arith]
  · rw [hc4]
    exact d4.congr xm (kx.gpr (by decide)) (kx.gpr (by decide)) (kx.gpr (by decide))
  · exact Keep.trans' uk ((((k1.trans k2).trans k3).trans k4).trans kx |>.mono (by decide))

/-- A step's pass over `k + 1` words (`passes kr`, `[kr] = k`): the same as `passLoop_ok`'s. -/
theorem passes_ok {s : State} {B : Addr} {Z dO dB k : Nat} (hs : Scr s B Z) {b : Bool} {kr : Reg}
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dB) (hk : s.gpr kr = BitVec.ofNat 64 k)
    (hkr : kr ∉ passRegs) (h3 : (s.gpr .t3).toNat ≤ 1) (h4 : (s.gpr .t4).toNat ≤ 1)
    (ha : s.gpr .a4 = dmask b) (hk' : k < 2 ^ 31) (hO8 : dO % 8 = 0) (hB8 : dB % 8 = 0)
    (hO : dO + 8 * (k + 1) ≤ Z) (hB : dB + 8 * (k + 1) ≤ Z)
    (dOB : dO + 8 * (k + 1) ≤ dB ∨ dB + 8 * (k + 1) ≤ dO) :
    WP isa (VG.Impl.Rsa.RISCV64.Div.passes kr) s fun t =>
      (t.gpr .t3).toNat ≤ 1 ∧ (t.gpr .t4).toNat ≤ 1 ∧ t.gpr .t6 = word t.mem B (dO + 8 * (k + 1 - 1)) ∧
      wordsVal t.mem B dO (k + 1) + 2 ^ (64 * (k + 1)) * ((t.gpr .t3).toNat + (t.gpr .t4).toNat) +
          (if b then wordsVal s.mem B dB (k + 1) + 1 else 0) =
        2 * wordsVal s.mem B dO (k + 1) + (s.gpr .t3).toNat + (s.gpr .t4).toNat +
          (if b then 2 ^ (64 * (k + 1)) else wordsVal s.mem B dB (k + 1)) ∧
      Outside B dO (8 * (k + 1)) s.mem t.mem ∧ Keep passRegs s t := by
  have hnw := hs.nowrap
  have hkr2 : kr ≠ .t2 := fun e => hkr (e ▸ by decide)
  unfold VG.Impl.Rsa.RISCV64.Div.passes
  rw [WP.seq_iff]
  have hb1 : WP isa (.block [.addi .t2 kr 1, .logicImm .and .t2 .t2 3]) s fun x =>
      (x.gpr .t2 = BitVec.ofNat 64 ((k + 1) % 4) ∧ x.mem = s.mem) ∧ Keep [.t2] s x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show 1 < 2048 by decide), hk, hkr2]
    rw [← BitVec.ofNat_add]; exact rem4_ofNat _ (by omega_arith)
  refine WP.mono hb1 fun x1 ⟨⟨x12, xm1⟩, kx1⟩ => ?_
  have sx1 : Scr x1 B Z := hs.congr kx1.2.2
  have hd0 : PassDone s x1 B dO dB b 0 :=
    (PassDone.zero h3 h4).congr xm1 (kx1.gpr (by decide)) (kx1.gpr (by decide)) (kx1.gpr (by decide))
  -- The first `(k + 1) mod 4` words, one at a time.
  have hq1 : WP isa (.ite (.zero .t2) (.block []) (countLoop .t2 passBody)) x1 fun y =>
      y.gpr .t0 = off B (dO + 8 * ((k + 1) % 4)) ∧ y.gpr .t1 = off B (dB + 8 * ((k + 1) % 4)) ∧
        PassDone s y B dO dB b ((k + 1) % 4) ∧ Keep passRegs x1 y := by
    refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega_arith) x12) (fun hz => ?_) (fun hz => ?_)
    · have hr : (k + 1) % 4 = 0 := of_decide_eq_true hz
      rw [hr]
      exact WP.block_nil ⟨by rw [kx1.gpr (by decide), h0]; rfl, by rw [kx1.gpr (by decide), h1]; rfl, hd0,
        Keep.refl _ _⟩
    · have hr : 1 ≤ (k + 1) % 4 := Nat.pos_of_ne_zero (of_decide_eq_false hz)
      refine WP.mono (passLoop_ok sx1 (b := b) (dO := dO) (dB := dB) (n := (k + 1) % 4)
        (by rw [kx1.gpr (by decide), h0]) (by rw [kx1.gpr (by decide), h1]) x12
        (by rw [kx1.gpr (by decide)]; exact h3) (by rw [kx1.gpr (by decide)]; exact h4)
        (by rw [kx1.gpr (by decide)]; exact ha) hr (by omega_arith) hO8 hB8 (by omega_arith) (by omega_arith)
        (by omega_arith)) fun y ⟨y0, y1, y3, y4, y6, yeq, yout, ky⟩ => ⟨y0, y1, ⟨y3, y4, fun _ => y6, ?_, ?_⟩, ky⟩
      · rw [xm1] at yout; exact yout
      · rw [xm1, kx1.gpr (r := .t3) (by decide), kx1.gpr (r := .t4) (by decide)] at yeq; exact yeq
  rw [WP.seq_iff]
  refine WP.mono hq1 fun y ⟨y0, y1, yd, ky⟩ => ?_
  rw [WP.seq_iff]
  have kxy : Keep passRegs s y := (kx1.trans ky).mono (by decide)
  have yk : y.gpr kr = BitVec.ofNat 64 k := (kxy.gpr hkr).trans hk
  have hb2 : WP isa (.block [.addi .t2 kr 1, .shift .srl .d .t2 .t2 2]) y fun x =>
      (x.gpr .t2 = BitVec.ofNat 64 ((k + 1) / 4) ∧ x.mem = y.mem) ∧ Keep [.t2] y x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show 1 < 2048 by decide), yk, hkr2]
    rw [← BitVec.ofNat_add]; exact quot4_ofNat _ (by omega_arith)
  refine WP.mono hb2 fun x2 ⟨⟨x22, xm2⟩, kx2⟩ => ?_
  have yd2 : PassDone s x2 B dO dB b ((k + 1) % 4) :=
    yd.congr xm2 (kx2.gpr (by decide)) (kx2.gpr (by decide)) (kx2.gpr (by decide))
  have hfin : ∀ u, PassDone s u B dO dB b (k + 1) → Keep passRegs s u →
      (u.gpr .t3).toNat ≤ 1 ∧ (u.gpr .t4).toNat ≤ 1 ∧ u.gpr .t6 = word u.mem B (dO + 8 * (k + 1 - 1)) ∧
      wordsVal u.mem B dO (k + 1) + 2 ^ (64 * (k + 1)) * ((u.gpr .t3).toNat + (u.gpr .t4).toNat) +
          (if b then wordsVal s.mem B dB (k + 1) + 1 else 0) =
        2 * wordsVal s.mem B dO (k + 1) + (s.gpr .t3).toNat + (s.gpr .t4).toNat +
          (if b then 2 ^ (64 * (k + 1)) else wordsVal s.mem B dB (k + 1)) ∧
      Outside B dO (8 * (k + 1)) s.mem u.mem ∧ Keep passRegs s u :=
    fun u ⟨u3, u4, u6, uo, ue⟩ uk => ⟨u3, u4, u6 (by omega_arith), ue, uo, uk⟩
  have kxy2 : Keep passRegs s x2 := (kxy.trans kx2).mono (by decide)
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega_arith) x22) (fun hz => ?_) (fun hz => ?_)
  · have hq : (k + 1) / 4 = 0 := of_decide_eq_true hz
    refine WP.block_nil (hfin x2 ?_ kxy2)
    rw [show k + 1 = (k + 1) % 4 by omega_arith]; exact yd2
  · have hq : 1 ≤ (k + 1) / 4 := Nat.pos_of_ne_zero (of_decide_eq_false hz)
    refine WP.mono (pass4Loop_ok hs (r := (k + 1) % 4) (g := (k + 1) / 4) yd2
      ((kxy2.2.2)) (by rw [kx2.gpr (by decide)]; exact y0) (by rw [kx2.gpr (by decide)]; exact y1) x22
      (by rw [kxy2.gpr (by decide), ha]) hq (by omega_arith) hO8 hB8 (by omega_arith) (by omega_arith)
      (by omega_arith)) fun u ⟨ud, uk⟩ => hfin u ?_ ((kxy2.trans uk).mono (by decide))
    rw [show k + 1 = (k + 1) % 4 + 4 * ((k + 1) / 4) by omega_arith]; exact ud

/-- The registers the final correction changes. -/
abbrev fixRegs : List Reg := [.t0, .t1, .t3, .t4, .t5, .t6, .a5]

/-- `[o] := [o] + ([d] ∧ mask)` over `n` words (`countLoop .t3 fixBody`), the carry in and out
in `t4`. -/
theorem fixLoop_ok {s : State} {B : Addr} {Z dO dB n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dB) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (h4 : (s.gpr .t4).toNat ≤ 1) (ha : s.gpr .a4 = dmask b)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO8 : dO % 8 = 0) (hB8 : dB % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hB : dB + 8 * n ≤ Z) (dOB : dO + 8 * n ≤ dB ∨ dB + 8 * n ≤ dO) :
    WP isa (countLoop .t3 fixBody) s fun t =>
      wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .t4).toNat =
        wordsVal s.mem B dO n + (s.gpr .t4).toNat + (if b then wordsVal s.mem B dB n else 0) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep fixRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dB + 8 * i) ∧ (t.gpr .t4).toNat ≤ 1 ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .t4).toNat =
        wordsVal s.mem B dO i + (s.gpr .t4).toNat + (if b then wordsVal s.mem B dB i else 0) ∧
      Keep fixRegs s t
  refine WP.mono (wp_countdown (body := .block (fixBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j4, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, h4, Outside.refl _ _ _ _, by cases b <;> simp [wordsVal],
      Keep.refl _ _⟩ h3)
    fun t ⟨_, _, _, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .a4 = dmask b := (jk.gpr (r := .a4) (by decide)).trans ha
  have hst : WP isa (.block (fixBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dB + 8 * i + 8) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dO + 8 * i) + t.gpr .t4 + (word t.mem B (dB + 8 * i) &&& dmask b)) ∧
        t'.gpr .t4 = ((if word t.mem B (dO + 8 * i) + t.gpr .t4 + (word t.mem B (dB + 8 * i) &&& dmask b) <
              word t.mem B (dB + 8 * i) &&& dmask b then (1 : BitVec 64) else 0) |||
          (if word t.mem B (dO + 8 * i) + t.gpr .t4 < t.gpr .t4 then 1 else 0))) ∧
      Keep fixRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fixBody, j0, j1, ja, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dB + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dB + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l3, lm, l4⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · rw [l4]; exact (adc64_arith _ _ _ j4).2
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wb : word t.mem B (dB + 8 * i) = word s.mem B (dB + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have k := (adc64_arith (word t.mem B (dO + 8 * i)) (t.gpr .t4) (word t.mem B (dB + 8 * i) &&& dmask b) j4).1
    rw [← l4, wa, wb] at k
    have hy : (word s.mem B (dB + 8 * i) &&& dmask b).toNat =
        if b then (word s.mem B (dB + 8 * i)).toNat else 0 := by
      rw [and_mask_eq]; cases b <;> rfl
    rw [hy] at k
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dB i,
      wordsVal_succ_top s.mem B dO i, Nat.mul_succ, Nat.pow_add, wa, wb]
    generalize word s.mem B (dO + 8 * i) + t.gpr .t4 + (word s.mem B (dB + 8 * i) &&& dmask b) = o at k ⊢
    generalize 2 ^ (64 * i) = P at jeq ⊢
    cases b
    · simp only [Bool.false_eq_true, ite_false] at k jeq ⊢
      grind
    · simp only [ite_true] at k jeq ⊢
      grind

/-! ## The quotient's words

The dividend's bits are taken from the top, a word at a time: while bit
`L + 63 - e` is the next (`64 ∣ L`, `e < 64`), word `L / 64` holds the
dividend's next `64 - e` bits above the quotient's last `e`, and the words
above it the quotient's earlier bits (`qv`). -/

/-- The words of `[q]` after the quotient's bits `q`, `e` of them in word `L / 64`. -/
def qv (N₀ q L e : Nat) : Nat :=
  N₀ % 2 ^ L + 2 ^ L * (2 ^ e * (N₀ / 2 ^ L % 2 ^ (64 - e)) + q % 2 ^ e) + 2 ^ L * 2 ^ 64 * (q / 2 ^ e)

/-- A number in three parts, the low one below `P` and the middle one a word. -/
theorem split3_unique {P lo x hi lo' x' hi' : Nat}
    (h : lo + P * x + P * 2 ^ 64 * hi = lo' + P * x' + P * 2 ^ 64 * hi')
    (hlo : lo < P) (hlo' : lo' < P) (hx : x < 2 ^ 64) (hx' : x' < 2 ^ 64) : lo = lo' ∧ x = x' ∧ hi = hi' := by
  have e : ∀ a y z : Nat, a + P * y + P * 2 ^ 64 * z = a + P * (y + 2 ^ 64 * z) := by
    intro a y z; rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  rw [e, e] at h
  have hP : 0 < P := by omega
  have m := congrArg (· % P) h
  have d := congrArg (· / P) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hlo'] at m
  simp only [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hlo, Nat.div_eq_of_lt hlo', Nat.zero_add] at d
  omega

/-- The word of `qv` is a word. -/
theorem qv_word_lt (N₀ q L : Nat) {e : Nat} (he : e ≤ 64) :
    2 ^ e * (N₀ / 2 ^ L % 2 ^ (64 - e)) + q % 2 ^ e < 2 ^ 64 := by
  have h1 := Nat.mod_lt (N₀ / 2 ^ L) (Nat.two_pow_pos (64 - e))
  have h2 := Nat.mod_lt q (Nat.two_pow_pos e)
  have h3 : 2 ^ e * (N₀ / 2 ^ L % 2 ^ (64 - e) + 1) ≤ 2 ^ e * 2 ^ (64 - e) := Nat.mul_le_mul_left _ h1
  rw [← Nat.pow_add, Nat.add_sub_cancel' he, Nat.mul_add, Nat.mul_one] at h3
  omega

/-- The next bit of the dividend is the top bit of the word. -/
theorem qv_bit (N₀ q L : Nat) {e : Nat} (he : e < 64) :
    (2 ^ e * (N₀ / 2 ^ L % 2 ^ (64 - e)) + q % 2 ^ e) / 2 ^ 63 = N₀ / 2 ^ (L + 63 - e) % 2 := by
  have p63 : 2 ^ 63 = 2 ^ e * 2 ^ (63 - e) := by rw [← Nat.pow_add]; congr 1; omega
  have p64 : 2 ^ (64 - e) = 2 ^ (63 - e) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  rw [p63, ← Nat.div_div_eq_div_mul, Nat.mul_add_div (Nat.two_pow_pos e),
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos e)), Nat.add_zero, p64, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, show L + (63 - e) = L + 63 - e by omega]

/-- The word shifted left with the quotient's next bit `c`. -/
theorem qv_shift (N₀ q L : Nat) {e c : Nat} (he : e < 64) (hc : c ≤ 1) :
    2 * (2 ^ e * (N₀ / 2 ^ L % 2 ^ (64 - e)) + q % 2 ^ e) % 2 ^ 64 + c =
        2 ^ (e + 1) * (N₀ / 2 ^ L % 2 ^ (64 - (e + 1))) + (2 * q + c) % 2 ^ (e + 1) ∧
      (2 * q + c) / 2 ^ (e + 1) = q / 2 ^ e := by
  have pe : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [Nat.pow_succ, Nat.mul_comm]
  have p64 : 2 ^ (64 - e) = 2 ^ (64 - (e + 1)) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have p : 2 ^ 64 = 2 ^ (e + 1) * 2 ^ (64 - (e + 1)) := by rw [← Nat.pow_add]; congr 1; omega
  -- `2 q + c` against `2^(e + 1)`.
  have hq := Nat.div_add_mod q (2 ^ e)
  have hr := Nat.mod_lt q (Nat.two_pow_pos e)
  have hqc : 2 * q + c = 2 ^ (e + 1) * (q / 2 ^ e) + (2 * (q % 2 ^ e) + c) := by
    rw [pe]; conv => lhs; rw [← hq]
    rw [Nat.mul_add, Nat.mul_assoc]; omega
  have hlt : 2 * (q % 2 ^ e) + c < 2 ^ (e + 1) := by rw [pe]; omega
  have hm : (2 * q + c) % 2 ^ (e + 1) = 2 * (q % 2 ^ e) + c := by
    rw [hqc, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hd : (2 * q + c) / 2 ^ (e + 1) = q / 2 ^ e := by
    rw [hqc, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.add_zero]
  refine ⟨?_, hd⟩
  rw [hm]
  -- The dividend's bits of the word: the top one shifted out.
  generalize N₀ / 2 ^ L = n
  have hn := Nat.div_add_mod (n % 2 ^ (64 - e)) (2 ^ (64 - (e + 1)))
  have hmm : n % 2 ^ (64 - e) % 2 ^ (64 - (e + 1)) = n % 2 ^ (64 - (e + 1)) :=
    Nat.mod_mod_of_dvd _ ⟨2, p64⟩
  rw [hmm] at hn
  have hm1 := Nat.mod_lt n (Nat.two_pow_pos (64 - (e + 1)))
  have hb : 2 * (2 ^ e * (n % 2 ^ (64 - e)) + q % 2 ^ e) =
      2 ^ 64 * (n % 2 ^ (64 - e) / 2 ^ (64 - (e + 1))) +
        (2 ^ (e + 1) * (n % 2 ^ (64 - (e + 1))) + 2 * (q % 2 ^ e)) := by
    rw [p, pe]
    conv => lhs; rw [← hn]
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  have hl : 2 ^ (e + 1) * (n % 2 ^ (64 - (e + 1))) + 2 * (q % 2 ^ e) < 2 ^ 64 := by
    have h3 : 2 ^ (e + 1) * (n % 2 ^ (64 - (e + 1)) + 1) ≤ 2 ^ (e + 1) * 2 ^ (64 - (e + 1)) :=
      Nat.mul_le_mul_left _ hm1
    rw [← p, Nat.mul_add, Nat.mul_one] at h3
    rw [pe] at h3 ⊢
    omega
  rw [hb, Nat.mul_add_mod, Nat.mod_eq_of_lt hl]
  omega

/-- A step of `qv`. -/
theorem qv_step (N₀ q L : Nat) {e c : Nat} (he : e < 64) (hc : c ≤ 1) :
    N₀ % 2 ^ L + 2 ^ L * (2 * (2 ^ e * (N₀ / 2 ^ L % 2 ^ (64 - e)) + q % 2 ^ e) % 2 ^ 64 + c) +
        2 ^ L * 2 ^ 64 * (q / 2 ^ e) = qv N₀ (2 * q + c) L (e + 1) := by
  obtain ⟨e1, e2⟩ := qv_shift N₀ q L he hc
  rw [qv, e2, e1]

/-- A word done: the next word's start. -/
theorem qv_next (N₀ q L : Nat) : qv N₀ q (L + 64) 64 = qv N₀ q L 0 := by
  simp only [qv, Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.zero_add, Nat.one_mul,
    Nat.div_one, Nat.sub_zero, Nat.mod_one, Nat.add_zero]
  have a : N₀ % 2 ^ (L + 64) = N₀ % 2 ^ L + 2 ^ L * (N₀ / 2 ^ L % 2 ^ 64) := by rw [Nat.pow_add, Nat.mod_mul]
  have b : 2 ^ (L + 64) * (q % 2 ^ 64) + 2 ^ (L + 64) * 2 ^ 64 * (q / 2 ^ 64) = 2 ^ L * 2 ^ 64 * q := by
    rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div, Nat.pow_add]
  rw [a, Nat.add_assoc, b]

/-- All the words done: the quotient. -/
theorem qv_done (N₀ q : Nat) : qv N₀ q 0 64 = q := by
  simp only [qv, Nat.pow_zero, Nat.mod_one, Nat.sub_self, Nat.mul_zero, Nat.zero_add, Nat.one_mul]
  exact Nat.mod_add_div q _

/-- No word done: the dividend. -/
theorem qv_start {N₀ L : Nat} (h : N₀ < 2 ^ (L + 64)) : qv N₀ 0 L 0 = N₀ := by
  simp only [qv, Nat.pow_zero, Nat.one_mul, Nat.mod_one, Nat.add_zero, Nat.zero_div, Nat.mul_zero,
    Nat.sub_zero]
  rw [← Nat.mod_mul, ← Nat.pow_add, Nat.mod_eq_of_lt h]

/-- A number of `k` words around its word `a`. -/
theorem wordsVal_mid (m : Mem) (B : Addr) {d k a : Nat} (ha : a < k) :
    wordsVal m B d k = wordsVal m B d a + 2 ^ (64 * a) * (word m B (d + 8 * a)).toNat +
      2 ^ (64 * a) * 2 ^ 64 * wordsVal m B (d + 8 * a + 8) (k - a - 1) := by
  have e := wordsVal_append m B d a (k - a)
  rw [Nat.add_sub_cancel' (Nat.le_of_lt ha), show k - a = (k - a - 1) + 1 by omega, wordsVal] at e
  rw [e, Nat.mul_add, Nat.mul_assoc]; exact (Nat.add_assoc _ _ _).symm

/-- Word `a` of `k` written. -/
theorem wordsVal_write_mid (m : Mem) (B : Addr) {d k a : Nat} (ha : a < k) (v : BitVec 64)
    (fit : d + 8 * k ≤ 2 ^ 64) :
    wordsVal (m.writeW (off B (d + 8 * a)) v) B d k = wordsVal m B d a + 2 ^ (64 * a) * v.toNat +
      2 ^ (64 * a) * 2 ^ 64 * wordsVal m B (d + 8 * a + 8) (k - a - 1) := by
  have o := writeW_outside m B (d := d + 8 * a) v (by omega_arith)
  rw [wordsVal_mid _ B ha, word_writeW_self, o.wordsVal (by omega_arith) (by omega_arith),
    o.wordsVal (by omega_arith) (by omega_arith)]

/-- The quotient's word index, from the count `j` of the bits left. -/
theorem qidx_ofNat {j : Nat} (h1 : 1 ≤ j) (h2 : j < 2 ^ 32) :
    (BitVec.ofNat 64 j - BitVec.ofNat 64 1) >>> 6 <<< 3 = BitVec.ofNat 64 (8 * ((j - 1) / 64)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- `qword q`: `t2` := the address of the word of `[q]` that holds bit `j - 1`. -/
theorem qword_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {q j : Nat} (hq : q < 2048)
    (h7 : s.gpr .s7 = BitVec.ofNat 64 j) (hj1 : 1 ≤ j) (hj : j < 2 ^ 32) {a : Nat} (hA : (j - 1) / 64 = a)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .t2 = off B (arr w q + 8 * a) → Keep [.t2, .t5] s t → t.mem = s.mem →
      WP isa (.block rest) t Q) :
    WP isa (.block (qword q ++ rest)) s Q := by
  rw [qword, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) hq ?_
  rw [WP.block_append_iff]
  have hb : WP isa (.block [.addi .t5 .s7 (-1), .shift .srl .d .t5 .t5 6, .shift .sll .d .t5 .t5 3,
      .add .t2 .t2 .t5]) (s.write .t2 (off B (arr w q))) fun t =>
        (t.gpr .t2 = off B (arr w q + 8 * a) ∧ t.mem = s.mem) ∧
          Keep [.t2, .t5] (s.write .t2 (off B (arr w q))) t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h7, qidx_ofNat hj1 hj, hA, off_add]
  exact WP.mono hb fun t ⟨⟨t2, tm⟩, kt⟩ => k t t2 (((Keep.write _ _ _).trans kt).mono (by decide)) tm

theorem mask_and_one (b : Bool) : (dmask b &&& BitVec.ofNat 64 1).toNat = if b then 1 else 0 := by
  cases b <;> decide

/-- The mask of a word's sign bit being clear. -/
theorem sign_mask (v : BitVec 64) :
    v >>> 63 - BitVec.ofNat 64 1 = dmask (decide (v.toNat / 2 ^ 63 = 0)) := by
  have e : (v >>> 63).toNat = v.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  rcases (show v.toNat / 2 ^ 63 = 0 ∨ v.toNat / 2 ^ 63 = 1 by omega) with z | z
  · rw [show v >>> 63 = 0#64 from BitVec.eq_of_toNat_eq (by rw [e, z]; rfl), z]; decide
  · rw [show v >>> 63 = 1#64 from BitVec.eq_of_toNat_eq (by rw [e, z]; rfl), z]; decide

/-- A register outside `divRegs` is outside its sublists. -/
theorem kr_nmem {kr : Reg} (h : kr ∉ divRegs) {rs : List Reg} (hs : ∀ x ∈ rs, x ∈ divRegs := by decide) :
    kr ∉ rs := fun m => h (hs _ m)

/-- A word shifted left with a bit in. -/
theorem shl_or_toNat (x c : BitVec 64) (hc : c.toNat ≤ 1) : (x <<< 1 ||| c).toNat = 2 * x.toNat % 2 ^ 64 + c.toNat := by
  obtain ⟨e, -⟩ := shl64_arith x c hc
  have e2 : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- A step of the division, run: the pass over the remainder's `k + 1` words, the new mask
from its sign, and the quotient's word `a = (j - 1) / 64` shifted with the new bit. -/
theorem step_run {s : State} {B : Addr} {Z w N q r d : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (hN : N ≤ 2048)
    (hqr : q ≠ r) (hqd : q ≠ d) (hrd : r ≠ d) {j : Nat} (h7 : s.gpr .s7 = BitVec.ofNat 64 j)
    (hj1 : 1 ≤ j) (hj : j ≤ 64 * w) {bm : Bool} (ha : s.gpr .a4 = dmask bm)
    {k : Nat} {kr : Reg} (hkr : s.gpr kr = BitVec.ofNat 64 k) (hk1 : 1 ≤ k) (hkw : k ≤ w)
    (hkd : kr ∉ divRegs) :
    WP isa (stepK q r d kr) s fun u => Ws u B Z w N ∧ Frame B w [q, r] [] s.mem u.mem ∧
      u.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧ Keep divRegs s u ∧
      u.gpr .a4 = dmask (decide ((word u.mem B (arr w r + 8 * k)).toNat / 2 ^ 63 = 0)) ∧
      (∃ C, numk u.mem B w r k + 2 ^ (64 * (k + 1)) * C + (if bm then numk s.mem B w d k + 1 else 0) =
        2 * numk s.mem B w r k + (word s.mem B (arr w q + 8 * ((j - 1) / 64))).toNat / 2 ^ 63 +
          (if bm then 1 else 0) + (if bm then 2 ^ (64 * (k + 1)) else numk s.mem B w d k)) ∧
      wordsVal u.mem B (arr w r + 8 * (k + 1)) (w - k) = wordsVal s.mem B (arr w r + 8 * (k + 1)) (w - k) ∧
      num u.mem B w q = wordsVal s.mem B (arr w q) ((j - 1) / 64) +
        2 ^ (64 * ((j - 1) / 64)) * (2 * (word s.mem B (arr w q + 8 * ((j - 1) / 64))).toNat % 2 ^ 64 +
          (if decide ((word u.mem B (arr w r + 8 * k)).toNat / 2 ^ 63 = 0) then 1 else 0)) +
        2 ^ (64 * ((j - 1) / 64)) * 2 ^ 64 *
          wordsVal s.mem B (arr w q + 8 * ((j - 1) / 64) + 8) (w - (j - 1) / 64 - 1) := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have dqr := arr_disj (w := w) hqr
  have dqd := arr_disj (w := w) hqd
  have drd := arr_disj (w := w) hrd
  have hjw : j < 2 ^ 32 := by omega_arith
  have haw : (j - 1) / 64 < w := by omega_arith
  obtain ⟨a, hA⟩ : ∃ a, (j - 1) / 64 = a := ⟨_, rfl⟩
  rw [hA] at haw ⊢
  rw [stepK, WP.seq_iff]
  simp only [List.append_assoc]
  -- The quotient's word and its top bit; the pointers; the carries.
  refine qword_ok h (show q < 2048 by omega_arith) h7 hj1 hjw hA fun x1 p2 k1 m1 => ?_
  have hx1 := h.of_keep k1
  rw [WP.block_append_iff]
  have hb2 : WP isa (.block [.load .d .t5 .t2 0, .shift .srl .d .t3 .t5 63]) x1 fun x =>
      (x.gpr .t3 = word s.mem B (arr w q + 8 * a) >>> 63 ∧ x.mem = s.mem) ∧ Keep [.t3, .t5] x1 x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [p2, add_ofNat_zero', hx1.scr.ld (show arr w q + 8 * a + 8 ≤ Z by omega_arith),
      hx1.scr.al8 (show arr w q + 8 * a + 8 ≤ Z by omega_arith) (by have := arr_al w q; omega_arith), m1]
  refine WP.mono hb2 fun x2 ⟨⟨x23, m2⟩, k2⟩ => ?_
  have k12 : Keep [.t2, .t3, .t5] s x2 := (k1.trans k2).mono (by decide)
  have hx2 := h.of_keep k12
  refine ptr2_ok hx2 (r := .t0) (r' := .t1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (show r < 2048 by omega_arith) (show d < 2048 by omega_arith) fun x3 p0 p1 k3 m3 => ?_
  have hx3 := hx2.of_keep k3
  have k3r : x3.gpr kr = BitVec.ofNat 64 k := by
    rw [k3.gpr (kr_nmem hkd), k2.gpr (kr_nmem hkd), k1.gpr (kr_nmem hkd), hkr]
  have hb3 : WP isa (.block [.logicImm .and .t4 .a4 1]) x3 fun x =>
      (x.gpr .t4 = x3.gpr .a4 &&& BitVec.ofNat 64 1 ∧ x.mem = x3.mem) ∧ Keep [.t4] x3 x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun []
  have hk4 : kr ≠ .t4 := fun e => hkd (e ▸ by decide)
  refine WP.mono hb3 fun x4 ⟨⟨x44, m4⟩, k4⟩ => ?_
  have x4k : x4.gpr kr = BitVec.ofNat 64 k := by rw [k4.gpr (by simp [hk4]), k3r]
  have hkp : kr ∉ passRegs := kr_nmem hkd
  have k14 : Keep [.t0, .t1, .t2, .t3, .t4, .t5] s x4 := ((k12.trans k3).trans k4).mono (by decide)
  have hx4 := h.of_keep k14
  have a4 : x4.gpr .a4 = dmask bm := (k14.gpr (r := .a4) (by decide)).trans ha
  have a3 : x3.gpr .a4 = dmask bm := ((k12.trans k3).gpr (r := .a4) (by decide)).trans ha
  have t3 : x4.gpr .t3 = word s.mem B (arr w q + 8 * a) >>> 63 := by
    rw [k4.gpr (r := .t3) (by decide), k3.gpr (r := .t3) (by decide), x23]
  have t0 : x4.gpr .t0 = off B (arr w r) := by rw [k4.gpr (r := .t0) (by decide), p0]
  have t1 : x4.gpr .t1 = off B (arr w d) := by rw [k4.gpr (r := .t1) (by decide), p1]
  have mx : x4.mem = s.mem := by rw [m4, m3, m2]
  rw [WP.seq_iff]
  refine WP.mono (passes_ok hx4.scr (b := bm) (dO := arr w r) (dB := arr w d) (k := k) t0 t1 x4k hkp
    (by rw [t3]; exact (shl64_arith _ 0 (by decide)).2) (by rw [x44, a3, mask_and_one]; split <;> decide)
    a4 (by omega_arith) (arr_al _ _) (arr_al _ _) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun y ⟨_, _, y6, yeq, yout, ky⟩ => ?_
  have hy := hx4.of_keep ky
  have k1y : Keep divRegs s y := Keep.trans' (k14.mono (by decide)) (ky.mono (by decide))
  -- The sign, the mask and the bit; the quotient's word.
  rw [WP.block_append_iff]
  have hb4 : WP isa (.block [.shift .srl .d .t5 .t6 63, .addi .a4 .t5 (-1), .logicImm .and .a5 .a4 1]) y
      fun x => (x.gpr .a4 = y.gpr .t6 >>> 63 - BitVec.ofNat 64 1 ∧
        x.gpr .a5 = (y.gpr .t6 >>> 63 - BitVec.ofNat 64 1) &&& BitVec.ofNat 64 1 ∧ x.mem = y.mem) ∧
        Keep [.t5, .a4, .a5] y x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun []
  refine WP.mono hb4 fun z ⟨⟨z4, z5, mz⟩, kz⟩ => ?_
  have hz := hy.of_keep kz
  have z7 : z.gpr .s7 = BitVec.ofNat 64 j := by
    rw [kz.gpr (r := .s7) (by decide), ky.gpr (r := .s7) (by decide), k14.gpr (r := .s7) (by decide), h7]
  refine qword_ok hz (show q < 2048 by omega_arith) z7 hj1 hjw hA fun z1 q2 kq mq => ?_
  have hz1 := hz.of_keep kq
  -- The quotient's word is not in the remainder's words.
  have wq : word z1.mem B (arr w q + 8 * a) = word s.mem B (arr w q + 8 * a) := by
    rw [mq, mz, yout.word (by omega_arith) (by omega_arith), mx]
  have hb5 : WP isa (.block [.load .d .t5 .t2 0, .shift .sll .d .t5 .t5 1, .logic .or .t5 .t5 .a5,
      .store .d .t5 .t2 0, .addi .s7 .s7 (-1)]) z1 fun x =>
        (x.mem = z1.mem.writeW (off B (arr w q + 8 * a)) (word z1.mem B (arr w q + 8 * a) <<< 1 ||| z1.gpr .a5) ∧
          x.gpr .s7 = z1.gpr .s7 - BitVec.ofNat 64 1) ∧ Keep [.t5, .s7] z1 x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [q2, add_ofNat_zero', hz1.scr.ld (show arr w q + 8 * a + 8 ≤ Z by omega_arith),
      hz1.scr.st (show arr w q + 8 * a + 8 ≤ Z by omega_arith),
      hz1.scr.al8 (show arr w q + 8 * a + 8 ≤ Z by omega_arith) (by have := arr_al w q; omega_arith)]
  refine WP.mono hb5 fun u ⟨⟨mu, u7⟩, ku⟩ => ?_
  have kzu : Keep divRegs y u := ((kz.trans kq).trans ku).mono (by decide)
  have oq := writeW_outside z1.mem B (d := arr w q + 8 * a)
    (word z1.mem B (arr w q + 8 * a) <<< 1 ||| z1.gpr .a5) (by omega_arith)
  rw [← mu] at oq
  have mzy : z1.mem = y.mem := by rw [mq, mz]
  -- The remainder's top word, and its sign.
  have wr : word u.mem B (arr w r + 8 * k) = y.gpr .t6 := by
    rw [oq.word (by omega_arith) (by omega_arith), mzy, y6, Nat.add_sub_cancel]
  have a5z : z1.gpr .a5 = z.gpr .a5 := kq.gpr (r := .a5) (by decide)
  have sgn := sign_mask (y.gpr .t6)
  have a5v : (z1.gpr .a5).toNat = if decide ((word u.mem B (arr w r + 8 * k)).toNat / 2 ^ 63 = 0) then 1 else 0 := by
    rw [a5z, z5, sgn, mask_and_one, wr]
  refine ⟨hz1.of_keep ku, ?_, ?_, Keep.trans' k1y kzu, ?_, ?_, ?_, ?_⟩
  · -- The frame: the remainder's words, then the quotient's word.
    have f1 : Frame B w [q, r] [] s.mem y.mem := by
      rw [← mx]; exact Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using yout) (by omega_arith) (by simp)
    have f2 : Frame B w [q, r] [] y.mem u.mem := by
      rw [← mzy]
      exact Frame.of_arr (o := q) (d := 8 * a) (n := 8) (by rw [mu]; exact writeW_outside _ _ _ (by omega_arith))
        (by omega_arith) (by simp)
    exact f1.trans f2
  · rw [u7, kq.gpr (r := .s7) (by decide), kz.gpr (r := .s7) (by decide), ky.gpr (r := .s7) (by decide),
      k14.gpr (r := .s7) (by decide)]
  · rw [ku.gpr (r := .a4) (by decide), kq.gpr (r := .a4) (by decide), z4, sgn, wr]
  · refine ⟨(y.gpr .t3).toNat + (y.gpr .t4).toNat, ?_⟩
    have ru : numk u.mem B w r k = numk y.mem B w r k := by
      rw [← mzy]; exact oq.wordsVal (by omega_arith) (by omega_arith)
    have r4 : numk x4.mem B w r k = numk s.mem B w r k := by rw [mx]
    have d4 : numk x4.mem B w d k = numk s.mem B w d k := by rw [mx]
    rw [ru]
    change wordsVal y.mem B (arr w r) (k + 1) + _ + _ = _
    rw [x44, a3, mask_and_one, t3, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at yeq
    change _ + _ + (if bm then numk x4.mem B w d k + 1 else 0) = 2 * numk x4.mem B w r k + _ + _ +
      (if bm then _ else numk x4.mem B w d k) at yeq
    rw [r4, d4] at yeq
    exact yeq
  · rw [oq.wordsVal (d := arr w r + 8 * (k + 1)) (k := w - k) (by omega_arith) (by omega_arith), mzy, ← mx]
    exact (yout.wordsVal (d := arr w r + 8 * (k + 1)) (k := w - k) (Or.inr (Nat.le_refl _)) (by omega_arith))
  · generalize decide ((word u.mem B (arr w r + 8 * k)).toNat / 2 ^ 63 = 0) = sb at a5v ⊢
    rw [mu, mzy]
    have wq' : word y.mem B (arr w q + 8 * a) = word s.mem B (arr w q + 8 * a) := by rw [← mzy]; exact wq
    have b5 : (z1.gpr .a5).toNat ≤ 1 := by rw [a5v]; split <;> decide
    change wordsVal _ B (arr w q) w = _
    rw [wordsVal_write_mid _ B (d := arr w q) haw _ (by omega_arith), shl_or_toNat _ _ b5, a5v, wq']
    have o1 : Outside B (arr w r) (8 * (k + 1)) x4.mem y.mem := yout
    rw [o1.wordsVal (d := arr w q) (k := a) (by omega_arith) (by omega_arith),
      o1.wordsVal (d := arr w q + 8 * a + 8) (k := w - a - 1) (by omega_arith) (by omega_arith), mx]

/-! ## The division's invariant -/

/-- After the dividend's bits but the low `j`: `R` and `Q` the remainder and the quotient
of the bits taken (`R < D`), the remainder's `k + 1` words `R` (`bm`) or `R - D` (mod `2^(64 (k + 1))`),
and `[q]` the quotient's bits and the dividend's low bits (`qv`). -/
def DivInv (m : Mem) (B : Addr) (w k q r D N₀ j : Nat) (bm : Bool) : Prop :=
  ∃ R Q L e, R < D ∧ R + D * Q = N₀ / 2 ^ j ∧
    numk m B w r k = (if bm then R else R + 2 ^ (64 * (k + 1)) - D) ∧
    L + 64 = j + e ∧ e ≤ 64 ∧ L % 64 = 0 ∧ num m B w q = qv N₀ Q L e

/-- The remainder after a pass: `T - D` mod `2^(64 (w + 1))`, whatever the mask. -/
theorem pass_rem {P D R T X W C : Nat} {bm : Bool} (hD : D < P) (hR : R < D)
    (hT : T ≤ 2 * R + 1) (hX : X = if bm then R else R + 2 ^ 64 * P - D) (hW : W < 2 ^ 64 * P)
    (h : W + 2 ^ 64 * P * C + (if bm then D + 1 else 0) =
      2 * X + (T - 2 * R) + (if bm then 1 else 0) + (if bm then 2 ^ 64 * P else D)) (hT' : 2 * R ≤ T) :
    W = if D ≤ T then T - D else T + 2 ^ 64 * P - D := by
  obtain ⟨P2, e2⟩ : ∃ P2, 2 ^ 64 * P = P2 := ⟨_, rfl⟩
  rw [e2] at hX hW h ⊢
  have hP2 : 2 * P ≤ P2 := by omega
  rcases C with _ | _ | _ | n
  · cases bm <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hX h <;> split <;> omega
  · cases bm <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hX h <;> split <;> omega
  · cases bm <;> simp only [Bool.false_eq_true, ite_true, ite_false, Nat.mul_succ] at hX h <;> split <;> omega
  · have : P2 * (n + 1 + 1 + 1) = P2 * n + P2 + P2 + P2 := by simp only [Nat.mul_succ]
    cases bm <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hX h <;> omega

/-- The remainder's sign: its top word's top bit is clear exactly when `D ≤ T`. -/
theorem sign_of_rem {P D T W lo tw : Nat} (hD : D < P)
    (hW : W = if D ≤ T then T - D else T + 2 ^ 64 * P - D) (hT : T < 2 * D)
    (hs : W = lo + P * tw) (hlo : lo < P) (htw : tw < 2 ^ 64) : tw / 2 ^ 63 = 0 ↔ D ≤ T := by
  by_cases hDT : D ≤ T
  · simp only [hDT, ite_true] at hW
    have : tw = 0 := by
      rcases Nat.eq_zero_or_pos tw with z | z
      · exact z
      · have := Nat.le_mul_of_pos_right P z; omega
    simp [this, hDT]
  · simp only [hDT, ite_false] at hW
    have : tw = 2 ^ 64 - 1 := by
      by_contra hne
      have : P * tw ≤ P * (2 ^ 64 - 2) := Nat.mul_le_mul_left _ (by omega)
      omega
    simp only [this, hDT, iff_false]; decide

/-- The dividend's bits above `j - 1`. -/
theorem div_pow_pred {N₀ j : Nat} (hj : 1 ≤ j) : N₀ / 2 ^ (j - 1) = 2 * (N₀ / 2 ^ j) + N₀ / 2 ^ (j - 1) % 2 := by
  have e : N₀ / 2 ^ j = N₀ / 2 ^ (j - 1) / 2 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hj]
  rw [e]; omega

/-- A step of the division keeps its invariant (`DivInv`), one bit further. -/
theorem step_ok {s : State} {B : Addr} {Z w N q r d : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (hN : N ≤ 2048)
    (hqr : q ≠ r) (hqd : q ≠ d) (hrd : r ≠ d) {j : Nat} (h7 : s.gpr .s7 = BitVec.ofNat 64 j)
    (hj1 : 1 ≤ j) (hj : j ≤ 64 * w) {bm : Bool} (ha : s.gpr .a4 = dmask bm)
    {k : Nat} {kr : Reg} (hkr : s.gpr kr = BitVec.ofNat 64 k) (hk1 : 1 ≤ k) (hkw : k ≤ w)
    (hkd : kr ∉ divRegs)
    {D N₀ : Nat} (hD : numk s.mem B w d k = D) (hDw : D < 2 ^ (64 * k)) :
    WP isa (stepK q r d kr) s fun u => Ws u B Z w N ∧ Frame B w [q, r] [] s.mem u.mem ∧
      u.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧ Keep divRegs s u ∧
      wordsVal u.mem B (arr w r + 8 * (k + 1)) (w - k) = wordsVal s.mem B (arr w r + 8 * (k + 1)) (w - k) ∧
      ∃ bm', u.gpr .a4 = dmask bm' ∧
        (0 < D → DivInv s.mem B w k q r D N₀ j bm → DivInv u.mem B w k q r D N₀ (j - 1) bm') := by
  refine WP.mono (step_run h hq hr hd hN hqr hqd hrd h7 hj1 hj ha hkr hk1 hkw hkd)
    fun u ⟨hu, fu, u7, ku, ua, ⟨C, hC⟩, hhi, hqv⟩ => ⟨hu, fu, u7, ku, hhi, _, ua, fun hD0 hI => ?_⟩
  obtain ⟨R, Q, L, e, hR, hRQ, hX, hLe, he, hL, hV⟩ := hI
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  -- The word of the quotient this step takes: `e < 64`.
  obtain ⟨L₀, e₀, hL₀, he₀, hL0, hV₀⟩ : ∃ L₀ e₀, L₀ + 64 = j + e₀ ∧ e₀ < 64 ∧ L₀ % 64 = 0 ∧
      num s.mem B w q = qv N₀ Q L₀ e₀ := by
    rcases Nat.lt_or_ge e 64 with he' | he'
    · exact ⟨L, e, hLe, he', hL, hV⟩
    · refine ⟨L - 64, 0, by omega, by decide, by omega, ?_⟩
      rw [hV, show e = 64 by omega, show L = L - 64 + 64 by omega, qv_next, Nat.add_sub_cancel]
  have hA : 64 * ((j - 1) / 64) = L₀ := by omega
  have haw : (j - 1) / 64 < w := by omega
  generalize (j - 1) / 64 = a at hA haw hC hqv
  subst hA
  -- The quotient's words around word `a`.
  have hmid := wordsVal_mid s.mem B (d := arr w q) haw
  have hlo := wordsVal_lt s.mem B (arr w q) a
  have hx := (word s.mem B (arr w q + 8 * a)).isLt
  obtain ⟨elo, ex, ehi⟩ := split3_unique (hmid.symm.trans hV₀) hlo (Nat.mod_lt _ (Nat.two_pow_pos _)) hx
    (qv_word_lt N₀ Q (64 * a) (Nat.le_of_lt he₀))
  -- The dividend's next bit.
  have hbit : (word s.mem B (arr w q + 8 * a)).toNat / 2 ^ 63 = N₀ / 2 ^ (j - 1) % 2 := by
    rw [ex, qv_bit N₀ Q (64 * a) he₀, show 64 * a + 63 - e₀ = j - 1 by omega]
  have hb2 : N₀ / 2 ^ (j - 1) % 2 ≤ 1 := by omega
  have hNj := div_pow_pred (N₀ := N₀) hj1
  -- The remainder after the pass, and its sign.
  have hP := Nat.two_pow_pos (64 * k)
  have eP2 : 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by
    rw [show 64 * (k + 1) = 64 + 64 * k by omega, Nat.pow_add]
  have hW1 := wordsVal_lt u.mem B (arr w r) (k + 1)
  change numk u.mem B w r k < _ at hW1
  rw [eP2] at hW1 hX hC
  rw [hD, hX, hbit] at hC
  have hrem := pass_rem (T := 2 * R + N₀ / 2 ^ (j - 1) % 2) hDw hR (by omega) rfl hW1
    (by rw [show 2 * R + N₀ / 2 ^ (j - 1) % 2 - 2 * R = N₀ / 2 ^ (j - 1) % 2 by omega]; exact hC) (by omega)
  have hsg := sign_of_rem hDw hrem (by omega) (wordsVal_succ_top u.mem B (arr w r) k) (wordsVal_lt _ _ _ _)
    (word u.mem B (arr w r + 8 * k)).isLt
  -- The new invariant.
  have hc : (if decide ((word u.mem B (arr w r + 8 * k)).toNat / 2 ^ 63 = 0) then 1 else 0) ≤ 1 := by
    split <;> decide
  refine ⟨if D ≤ 2 * R + N₀ / 2 ^ (j - 1) % 2 then 2 * R + N₀ / 2 ^ (j - 1) % 2 - D
      else 2 * R + N₀ / 2 ^ (j - 1) % 2,
    2 * Q + (if decide ((word u.mem B (arr w r + 8 * k)).toNat / 2 ^ 63 = 0) then 1 else 0), 64 * a, e₀ + 1,
    ?_, ?_, ?_, by omega, by omega, by omega, ?_⟩
  · split <;> omega
  · have e1 : ∀ c, D * (2 * Q + c) = 2 * (D * Q) + D * c := fun c => by rw [Nat.mul_add, Nat.mul_left_comm]
    rw [e1]
    by_cases hDT : D ≤ 2 * R + N₀ / 2 ^ (j - 1) % 2
    · simp only [hDT, decide_eq_true (hsg.mpr hDT), ite_true, Nat.mul_one]
      omega
    · simp only [hDT, decide_eq_false (fun z => hDT (hsg.mp z)), Bool.false_eq_true, ite_false, Nat.mul_zero]
      omega
  · rw [eP2, hrem]
    by_cases hDT : D ≤ 2 * R + N₀ / 2 ^ (j - 1) % 2
    · simp only [hDT, decide_eq_true (hsg.mpr hDT), ite_true]
    · simp only [hDT, decide_eq_false (fun z => hDT (hsg.mp z)), Bool.false_eq_true, ite_false]
  · rw [hqv, elo, ex, ehi, qv_step N₀ Q (64 * a) he₀ hc]

/-! ## The division -/

/-- `li` of -1. -/
theorem exec_li_ones {s : State} {d : Reg} : exec (.li d (-1)) s = some (s.write d (BitVec.allOnes 64)) := by
  rw [exec_li (by decide)]; rfl

theorem shl6_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 6 = BitVec.ofNat 64 (64 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `init r`: the remainder's `w + 1` words := 0, `64 w` steps to count in `s7`, and the mask
of subtracting in `a4`. -/
theorem init_ok {s : State} {B : Addr} {Z w N r : Nat} (h : Ws s B Z w N) (hr : r < N)
    (hN : N ≤ 2048) :
    WP isa (init r) s fun u => Ws u B Z w N ∧ Frame B w [r] [] s.mem u.mem ∧
      num1 u.mem B w r = 0 ∧ u.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ u.gpr .a4 = dmask true ∧
      Keep [.t0, .t3, .t5, .a4, .s7] s u := by
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  rw [init, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (show r < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.addi .t3 .s9 1, .li .t5 0]) (s.write .t0 (off B (arr w r))) fun u =>
      (u.gpr .t0 = off B (arr w r) ∧ u.gpr .t3 = BitVec.ofNat 64 (w + 1) ∧ u.gpr .t5 = 0 ∧
        u.mem = s.mem) ∧ Keep [.t3, .t5] (s.write .t0 (off B (arr w r))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_addi_nat (show 1 < 2048 by decide), fin64_exec_li_zero, h.s9]
    exact (BitVec.ofNat_add _ _).symm
  refine WP.mono hb fun u ⟨⟨u0, u3, u5, mu⟩, ku⟩ => ?_
  have k₁ : Keep [.t0, .t3, .t5, .a4, .s7] s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [WP.seq_iff]
  refine WP.mono (zeroLoop_ok hu.scr u0 u3 u5 (by omega_arith) (by omega_arith) (arr_al _ _) (by omega_arith))
    fun v ⟨z, out, kv⟩ => ?_
  have k₂ : Keep [.t0, .t3, .t5, .a4, .s7] s v := Keep.trans' k₁ (kv.mono (by decide))
  have hv : Ws v B Z w N := h.of_keep k₂
  have hl : WP isa (.block [.shift .sll .d .s7 .s9 6, .li .a4 (-1)]) v fun x =>
      (x.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ x.gpr .a4 = BitVec.allOnes 64 ∧ x.mem = v.mem) ∧
        Keep [.s7, .a4] v x := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [hv.s9, shl6_ofNat w, exec_li_ones]
  refine WP.mono hl fun x ⟨⟨x7, x4, xm⟩, kx⟩ =>
    ⟨hv.of_keep kx, ?_, ?_, x7, x4, Keep.trans' k₂ (kx.mono (by decide))⟩
  · rw [xm, ← mu]
    exact Frame.of_arr (d := 0) (by simpa using out) (by omega_arith) (by simp)
  · rw [xm]; exact z

theorem mask_xor_ones (b : Bool) : dmask b ^^^ BitVec.allOnes 64 = dmask (!b) := by cases b <;> decide

/-- `fix r d`: the divisor added back to a negative remainder (`bm` false). -/
theorem fix_ok {s : State} {B : Addr} {Z w N r d : Nat} (h : Ws s B Z w N) (hr : r < N) (hd : d < N)
    (hN : N ≤ 2048) (hrd : r ≠ d) {bm : Bool} (ha : s.gpr .a4 = dmask bm)
    {k : Nat} {kr : Reg} (hkr : s.gpr kr = BitVec.ofNat 64 k) (hkw : k ≤ w) (hkd : kr ∉ divRegs) :
    WP isa (fixK r d kr) s fun u => Ws u B Z w N ∧ Frame B w [r] [] s.mem u.mem ∧ Keep divRegs s u ∧
      u.gpr .s7 = s.gpr .s7 ∧
      wordsVal u.mem B (arr w r + 8 * (k + 1)) (w - k) = wordsVal s.mem B (arr w r + 8 * (k + 1)) (w - k) ∧
      ∃ c, numk u.mem B w r k + 2 ^ (64 * (k + 1)) * c =
        numk s.mem B w r k + (if bm then 0 else numk s.mem B w d k) := by
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have drd := arr_disj (w := w) hrd
  rw [fixK, WP.seq_iff]
  refine ptr2_ok h (r := .t0) (r' := .t1) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (show r < 2048 by omega_arith) (show d < 2048 by omega_arith) fun x p0 p1 kx mx => ?_
  have hx := h.of_keep kx
  have xkr : x.gpr kr = BitVec.ofNat 64 k := by rw [kx.gpr (kr_nmem hkd), hkr]
  have hb : WP isa (.block [.logicImm .xor .a4 .a4 (-1), .li .t4 0, .addi .t3 kr 1]) x fun y =>
      (y.gpr .a4 = x.gpr .a4 ^^^ BitVec.allOnes 64 ∧ y.gpr .t4 = 0 ∧ y.gpr .t3 = BitVec.ofNat 64 (k + 1) ∧
        y.mem = x.mem) ∧ Keep [.a4, .t3, .t4] x y := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    have hk4 : kr ≠ .t4 := fun e => hkd (e ▸ by decide)
    have hka : kr ≠ .a4 := fun e => hkd (e ▸ by decide)
    brun [exec_addi_nat (show 1 < 2048 by decide), fin64_exec_li_zero, xkr, hk4, hka]
    exact ⟨congrArg _ (by decide), (BitVec.ofNat_add _ _).symm⟩
  refine WP.mono hb fun y ⟨⟨y4, y0, y3, my⟩, ky⟩ => ?_
  have kxy : Keep [.t0, .t1, .a4, .t3, .t4] s y := (kx.trans ky).mono (by decide)
  have hy := h.of_keep kxy
  have a4 : y.gpr .a4 = dmask (!bm) := by
    rw [y4, (kx.gpr (r := .a4) (by decide)).trans ha, mask_xor_ones]
  refine WP.mono (fixLoop_ok hy.scr (b := !bm) (dO := arr w r) (dB := arr w d) (n := k + 1)
    (by rw [ky.gpr (r := .t0) (by decide), p0]) (by rw [ky.gpr (r := .t1) (by decide), p1]) y3
    (by rw [y0]; decide) a4 (by omega_arith) (by omega_arith) (arr_al _ _) (arr_al _ _) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun u ⟨ueq, uout, ku⟩ => ?_
  refine ⟨hy.of_keep ku, ?_, Keep.trans' (kxy.mono (by decide)) (ku.mono (by decide)),
    (ku.gpr (r := .s7) (by decide)).trans (kxy.gpr (r := .s7) (by decide)), ?_, (u.gpr .t4).toNat, ?_⟩
  · rw [← mx, ← my]; exact Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using uout) (by omega_arith) (by simp)
  · rw [uout.wordsVal (d := arr w r + 8 * (k + 1)) (k := w - k) (Or.inr (Nat.le_refl _)) (by omega_arith), my, mx]
  · change wordsVal u.mem B (arr w r) (k + 1) + _ = wordsVal s.mem B (arr w r) (k + 1) + _
    rw [ueq, y0, my, mx]
    cases bm <;> rfl

/-- The count after a step. -/
theorem count_sub {N i : Nat} (hi : i < N) :
    BitVec.ofNat 64 (N - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The remainder and the quotient of `N = R + D Q`, `R < D`. -/
theorem divmod_of {N D R Q : Nat} (hR : R < D) (h : R + D * Q = N) : N / D = Q ∧ N % D = R := by
  subst h
  have hD : 0 < D := by omega
  rw [Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt hR, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hR]
  exact ⟨rfl, rfl⟩

/-- The `k + 1` words of an array outside the frame. -/
theorem Frame.numk {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {j k : Nat} (hk : k ≤ w) (hj : ∀ i ∈ js, i ≠ j) (hd : ∀ d ∈ ds, d + 8 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) : numk m' B w j k = numk m B w j k := by
  have hS : S w = 8 * (w + 2) := rfl
  exact h.words (fun i hi => by have := arr_disj (w := w) (hj i hi); omega_arith)
    (fun d hd' => by have := hd d hd'; have := hdr_le_arr w j; omega_arith) (by omega_arith)

/-- `divK q r d kr`, `kr` holding `k ≤ w`: `[q] := [q] / [d]` and `[r] := [q] mod [d]`, when
`[d] > 0` fits in `k` words: the passes are over `k + 1` words, and the remainder's words above
them stay as `init` zeroed them. -/
theorem divK_ok {s : State} {B : Addr} {Z w N q r d : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (hN : N ≤ 2048) (hqr : q ≠ r) (hqd : q ≠ d) (hrd : r ≠ d)
    {k : Nat} {kr : Reg} (hkr : s.gpr kr = BitVec.ofNat 64 k) (hk1 : 1 ≤ k) (hkw : k ≤ w)
    (hkd : kr ∉ divRegs)
    (hdk : numk s.mem B w d k = num s.mem B w d) (hDk : num s.mem B w d < 2 ^ (64 * k)) :
    WP isa (divK q r d kr) s fun u => Ws u B Z w N ∧
      Frame B w [q, r] [] s.mem u.mem ∧ Keep divRegs s u ∧ u.gpr .s7 = 0 ∧
      (0 < num s.mem B w d →
        num u.mem B w q = num s.mem B w q / num s.mem B w d ∧
        num1 u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        num u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        word u.mem B (arr w r + 8 * w) = 0) := by
  have fd := h.arr_fit hd
  have fr := h.arr_fit hr
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have hN₀ : num s.mem B w q < 2 ^ (64 * w) := wordsVal_lt _ _ _ _
  have hK : 64 * w < 2 ^ 64 := by omega_arith
  rw [divK, WP.seq_iff]
  refine WP.mono (init_ok h hr hN) fun u ⟨hu, km, z, u7, u4, ku⟩ => ?_
  rw [WP.seq_iff]
  have ukr : u.gpr kr = BitVec.ofNat 64 k := by rw [ku.gpr (kr_nmem hkd), hkr]
  -- The remainder's words: all zero.
  have zl : numk u.mem B w r k = 0 := by
    have := wordsVal_zero_part (a := 0) (c := k + 1) z (by omega)
    simpa using this
  have zh : wordsVal u.mem B (arr w r + 8 * (k + 1)) (w - k) = 0 :=
    wordsVal_zero_part (a := k + 1) (c := w - k) z (by omega)
  let D := num s.mem B w d
  let N₀ := num s.mem B w q
  let Inv : Nat → State → Prop := fun i x =>
    Ws x B Z w N ∧ Frame B w [q, r] [] s.mem x.mem ∧ Keep divRegs s x ∧
      x.gpr .s7 = BitVec.ofNat 64 (64 * w - i) ∧
      wordsVal x.mem B (arr w r + 8 * (k + 1)) (w - k) = 0 ∧
      ∃ bm, x.gpr .a4 = dmask bm ∧ (0 < D → DivInv x.mem B w k q r D N₀ (64 * w - i) bm)
  have i0 : Inv 0 u := by
    refine ⟨hu, km.mono, ku.mono (by decide), by rw [u7, Nat.sub_zero], zh, true, u4, fun _ => ?_⟩
    refine ⟨0, 0, 64 * (w - 1), 0, by omega, ?_, by rw [zl]; rfl, by omega, by decide, by omega, ?_⟩
    · rw [Nat.sub_zero, Nat.div_eq_of_lt hN₀]; rfl
    · rw [Frame.num km (by simp; omega_arith) (by simp) (by have := h.fit64 hq; omega_arith),
        qv_start (by rw [show 64 * (w - 1) + 64 = 64 * w by omega]; exact hN₀)]
  refine WP.mono (wp_countdown (body := stepK q r d kr) (cnt := .s7) (N := 64 * w)
    hK (by omega_arith) Inv (fun i hi x ⟨hx, kx, rx, cx, zx, bm, xa, vx⟩ _ => ?_) i0 u7)
    fun x ⟨hx, kx, rx, cx, zx, bm, xa, vx⟩ => ?_
  · have dx : numk x.mem B w d k = D := by
      rw [Frame.numk kx hkw (by simp; omega_arith) (by simp) (by omega_arith), hdk]
    have xkr : x.gpr kr = BitVec.ofNat 64 k := by rw [rx.gpr hkd, hkr]
    refine WP.mono (step_ok hx hq hr hd hN hqr hqd hrd cx (j := 64 * w - i) (by omega) (by omega) xa
      xkr hk1 hkw hkd (N₀ := N₀) dx hDk) fun y ⟨hy, ky, y7, ry, yh, bm', ya, vy⟩ =>
        ⟨⟨hy, kx.trans ky, Keep.trans' rx ry, by rw [y7, cx, count_sub hi], by rw [yh, zx], bm', ya,
          fun hD0 => ?_⟩, y7⟩
    rw [show 64 * w - (i + 1) = 64 * w - i - 1 by omega]
    exact vy hD0 (vx hD0)
  · have dx : numk x.mem B w d k = D := by
      rw [Frame.numk kx hkw (by simp; omega_arith) (by simp) (by omega_arith), hdk]
    have xkr : x.gpr kr = BitVec.ofNat 64 k := by rw [rx.gpr hkd, hkr]
    refine WP.mono (fix_ok hx hr hd hN hrd xa xkr hkw hkd) fun v ⟨hv, kv, rv, v7, vh, c, hc⟩ =>
      ⟨hv, kx.trans kv.mono, Keep.trans' rx rv, by rw [v7, cx, Nat.sub_self]; rfl, fun hD0 => ?_⟩
    obtain ⟨R, Q, L, e, hR, hRQ, hX, hLe, he, -, hV⟩ := vx hD0
    rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hRQ
    rw [show L = 0 by omega, show e = 64 by omega, qv_done] at hV
    obtain ⟨eq, er⟩ := divmod_of hR hRQ
    have hP := Nat.two_pow_pos (64 * k)
    have eP2 : 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by
      rw [show 64 * (k + 1) = 64 + 64 * k by omega, Nat.pow_add]
    have hW := wordsVal_lt v.mem B (arr w r) (k + 1)
    change numk v.mem B w r k < _ at hW
    rw [hX, dx, eP2] at hc
    rw [eP2] at hW
    -- The remainder after the correction.
    have hRv : numk v.mem B w r k = R := by
      obtain ⟨P2, e2⟩ : ∃ P2, 2 ^ 64 * 2 ^ (64 * k) = P2 := ⟨_, rfl⟩
      rw [e2] at hc hW
      have : D < P2 := by omega
      rcases c with _ | _ | c
      · cases bm <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hc <;> omega
      · cases bm <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hc <;> omega
      · have : P2 * (c + 1 + 1) = P2 * c + P2 + P2 := by simp only [Nat.mul_succ]
        cases bm <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hc <;> omega
    -- All its `w + 1` words.
    have hR1 : num1 v.mem B w r = R := by
      have e := wordsVal_append v.mem B (arr w r) (k + 1) (w - k)
      rw [show k + 1 + (w - k) = w + 1 by omega, vh, zx, Nat.mul_zero, Nat.add_zero] at e
      change num1 v.mem B w r = _ at e
      rw [e]; exact hRv
    have qv' : num v.mem B w q = num x.mem B w q :=
      Frame.num kv (by simp; omega_arith) (by simp) (by have := h.fit64 hq; omega_arith)
    have hlt : R < 2 ^ (64 * w) := by
      have : 2 ^ (64 * k) ≤ 2 ^ (64 * w) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have e3 := num1_eq v.mem B w r
    have hw0 : (word v.mem B (arr w r + 8 * w)).toNat = 0 := by
      rcases Nat.eq_zero_or_pos (word v.mem B (arr w r + 8 * w)).toNat with e | e
      · exact e
      · have : 2 ^ (64 * w) ≤ 2 ^ (64 * w) * (word v.mem B (arr w r + 8 * w)).toNat :=
          Nat.le_mul_of_pos_right _ e
        omega_arith
    refine ⟨by rw [qv', hV, eq], by rw [hR1, er], ?_, BitVec.eq_of_toNat_eq (by rw [hw0]; rfl)⟩
    rw [hw0, Nat.mul_zero, Nat.add_zero] at e3
    rw [← e3, hR1, er]

/-- `Div.div q r d t`: `[q] := [q] / [d]`, `[r] := [q] mod [d]` (its `w + 1` words, so word `w`
is zero), when `[d] > 0` and its word `w` is zero; `t` is not used. -/
theorem div_ok {s : State} {B : Addr} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (_ht : t < N) (hN : N ≤ 2048)
    (hqr : q ≠ r) (hqd : q ≠ d) (_hqt : q ≠ t) (hrd : r ≠ d) (_hrt : r ≠ t) (_hdt : d ≠ t)
    (hdz : word s.mem B (arr w d + 8 * w) = 0) :
    WP isa (div q r d t) s fun u => Ws u B Z w N ∧
      Frame B w [q, r, t] [] s.mem u.mem ∧ Keep divRegs s u ∧ u.gpr .s7 = 0 ∧
      (0 < num s.mem B w d →
        num u.mem B w q = num s.mem B w q / num s.mem B w d ∧
        num1 u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        num u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        word u.mem B (arr w r + 8 * w) = 0) := by
  have hD : numk s.mem B w d w = num s.mem B w d := by
    change num1 s.mem B w d = _
    rw [num1_eq, hdz]; rfl
  exact WP.mono (divK_ok h hq hr hd hN hqr hqd hrd h.s9 h.wpos (Nat.le_refl _) (by decide) hD (wordsVal_lt _ _ _ _)) fun u ⟨hu, f, k, u7, v⟩ => ⟨hu, f.mono, k, u7, v⟩

/-! ## The division over the divisor's words -/

/-- The `k + 1` low words of a number below `2^(64 k)` whose extra word is 0. -/
theorem numk_of_lt {m : Mem} {B : Addr} {w d k : Nat} (hz : word m B (arr w d + 8 * w) = 0)
    (hkw : k ≤ w) (hlt : num m B w d < 2 ^ (64 * k)) : numk m B w d k = num m B w d := by
  rcases Nat.lt_or_ge k w with hk | hk
  · have e := wordsVal_append m B (arr w d) (k + 1) (w - (k + 1))
    rw [Nat.add_sub_cancel' (by omega)] at e
    have hp : 2 ^ (64 * k) ≤ 2 ^ (64 * (k + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have h0 : wordsVal m B (arr w d + 8 * (k + 1)) (w - (k + 1)) = 0 := by
      refine Nat.eq_zero_of_not_pos fun hpos => ?_
      have := Nat.le_mul_of_pos_right (2 ^ (64 * (k + 1))) hpos
      have : num m B w d = wordsVal m B (arr w d) w := rfl
      omega
    change wordsVal m B (arr w d) (k + 1) = wordsVal m B (arr w d) w
    rw [e, h0, Nat.mul_zero]
    exact (Nat.add_zero _).symm
  · obtain rfl : k = w := by omega
    change num1 m B k d = _
    rw [num1_eq, hz]; rfl

theorem add7_shr3_ofNat (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := k) (by omega_arith), Nat.mod_eq_of_lt (a := 7) (by decide),
    Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- `wordsOf len`: `s8 := ⌈L / 8⌉`. -/
theorem wordsOf_ok {s : State} {len : Reg} {L : Nat} (hl : s.gpr len = BitVec.ofNat 64 L) (hL : L < 2 ^ 32) :
    WP isa (.block (wordsOf len)) s fun t =>
      (t.gpr .s8 = BitVec.ofNat 64 ((L + 7) / 8) ∧ t.mem = s.mem) ∧ Keep [.s8] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [wordsOf, hl, add7_shr3_ofNat L hL]

/-- `divL q r d len`: `div`'s results for a divisor below `2^(8 L)`, `L` bytes
in `len`, its steps over the divisor's `⌈L / 8⌉` words. -/
theorem divL_ok {s : State} {B : Addr} {Z w N q r d : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (hN : N ≤ 2048) (hqr : q ≠ r) (hqd : q ≠ d) (hrd : r ≠ d)
    {len : Reg} {L : Nat} (hl : s.gpr len = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hLw : L ≤ 8 * w)
    (hdz : word s.mem B (arr w d + 8 * w) = 0) (hD : num s.mem B w d < 2 ^ (8 * L)) :
    WP isa (divL q r d len) s fun u => Ws u B Z w N ∧
      Frame B w [q, r] [] s.mem u.mem ∧ Keep (.s8 :: divRegs) s u ∧ u.gpr .s7 = 0 ∧
      (0 < num s.mem B w d →
        num u.mem B w q = num s.mem B w q / num s.mem B w d ∧
        num1 u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        num u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        word u.mem B (arr w r + 8 * w) = 0) := by
  have := h.wle
  rw [divL, WP.seq_iff]
  refine WP.mono (wordsOf_ok hl (by omega)) fun t ⟨⟨t8, tm⟩, kt⟩ => ?_
  have ht := h.of_keep kt
  have hDk : num t.mem B w d < 2 ^ (64 * ((L + 7) / 8)) := by
    rw [tm]; exact Nat.lt_of_lt_of_le hD (Nat.pow_le_pow_right (by decide) (by omega))
  have hdk : numk t.mem B w d ((L + 7) / 8) = num t.mem B w d :=
    numk_of_lt (by rw [tm]; exact hdz) (by omega) hDk
  refine WP.mono (divK_ok ht hq hr hd hN hqr hqd hrd t8 (by omega) (by omega) (by decide) hdk hDk)
    fun u ⟨hu, f, k, u7, v⟩ => ?_
  rw [tm] at f v
  exact ⟨hu, f, (kt.trans k).mono (by decide), u7, v⟩

end VG.Proof.Rsa.RISCV64.Keys
