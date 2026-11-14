module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.InvBatch
public import VerifiedGarbage.Proof.Rsa.PPC64LE.WordLoops
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# The word loops of the batched inverse on PPC64LE

Over `n` words of 64 bits at byte offsets of the working space (`Scr s B Z`),
pointers in `r5`–`r7` and the count in `r8`, as `WordLoops.lean`'s (whose
`subWLoop_ok`, `selWLoop_ok`, `copyWLoop_ok` and `eqWLoop_ok` the inverse
also uses):

* `macWLoop_ok`: `[o] := [a] + k [b]`, `k` in `r11`, the carry in and out in
  `r9`;
* `zerosW_ok`: `[o] := 0`;
* `fgLoop_ok`: a batch's pass over `f` and `g` (`fgBody`), two signed
  accumulators (`FGAcc`, `r22`–`r23` and `r24`–`r25`) whose low words,
  shifted by 59, are stored a word down, in place;
* `abLoop_ok` (`abLoop?_ok` when it may run no word): the pass over `a` and
  `b` (`abBody`), two signed accumulators with `k m` added to each low word
  by an unsigned carry (`ABAcc`), the sums stored a word down, in place.

The output of `mac` may be an input, or come before it, or be apart from it
(`AheadW`): a word is read before any word at or after it is written.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Loops

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.InvBatch (macWBody zerosW fgBody fterms fterm fout fshift abBody fmac)

/-! ## `mac` -/

/-- The registers `mac`'s loop changes: `loopRegs` and `r12`. -/
abbrev macRegs : List Reg := [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r12]

/-- A word of `a + k b + c`, by the carry bit: the low word and the carry. -/
theorem macW_arith (k b a c : Nat) (hk : k < 2 ^ 64) (hb : b < 2 ^ 64) (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    let x1 := k * b % 2 ^ 64 + a
    let x2 := k * b / 2 ^ 64 % 2 ^ 64 + (decide (2 ^ 64 ≤ x1)).toNat
    let x3 := x1 % 2 ^ 64 + c
    let x4 := x2 % 2 ^ 64 + (decide (2 ^ 64 ≤ x3)).toNat
    x3 % 2 ^ 64 + 2 ^ 64 * (x4 % 2 ^ 64) = a + k * b + c := by
  dsimp only
  have hkb : k * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_using [hk]) (by omega_using [hb])
  have e1 : k * b / 2 ^ 64 % 2 ^ 64 = k * b / 2 ^ 64 := Nat.mod_eq_of_lt (by omega_using [hkb])
  rw [e1]
  generalize k * b = P at hkb ⊢
  by_cases h1 : 2 ^ 64 ≤ P % 2 ^ 64 + a <;> by_cases h3 : 2 ^ 64 ≤ (P % 2 ^ 64 + a) % 2 ^ 64 + c <;>
    simp only [h1, h3, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- `[o] := [a] + k [b]` over `n` words (`countLoop .r8 macWBody`), from the
carry `c` in `r9`: the sum and the carry out. -/
theorem macWLoop_ok {s : State} {B : Addr} {Z dO dA dM n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dM)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO : dO + 8 * n ≤ Z) (hA : dA + 8 * n ≤ Z) (hM : dM + 8 * n ≤ Z)
    (aA : AheadW dO dA n) (aM : AheadW dO dM n) :
    WP isa (countLoop .r8 macWBody) s fun t =>
      wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .r9).toNat =
        wordsVal s.mem B dA n + (s.gpr .r11).toNat * wordsVal s.mem B dM n + (s.gpr .r9).toNat ∧
      t.gpr .r5 = off B (dO + 8 * n) ∧ Outside B dO (8 * n) s.mem t.mem ∧ Keep macRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ t.gpr .r6 = off B (dA + 8 * i) ∧ t.gpr .r7 = off B (dM + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .r9).toNat =
        wordsVal s.mem B dA i + (s.gpr .r11).toNat * wordsVal s.mem B dM i + (s.gpr .r9).toNat ∧
      Keep macRegs s t
  refine WP.mono (wp_countdown (body := .block (macWBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, j7, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h8)
    fun t ⟨j5, _, _, jout, jeq, jk⟩ => ⟨jeq, j5, jout, jk⟩
  have k11 : t.gpr .r11 = s.gpr .r11 := jk.gpr .r11 (by decide)
  have hst := (show WP isa (.block (macWBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      let bw := word t.mem B (dM + 8 * i)
      let aw := word t.mem B (dA + 8 * i)
      let v1 := (t.gpr .r11 * bw).toNat + aw.toNat
      let v2 := (BitVec.ofNat 64 ((t.gpr .r11).toNat * bw.toNat / 2 ^ 64)).toNat + (decide (2 ^ 64 ≤ v1)).toNat
      let v3 := (BitVec.ofNat 64 v1).toNat + (t.gpr .r9).toNat
      let v4 := (BitVec.ofNat 64 v2).toNat + (decide (2 ^ 64 ≤ v3)).toNat
      (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧ t'.gpr .r6 = off B (dA + 8 * i + 8) ∧
        t'.gpr .r7 = off B (dM + 8 * i + 8) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.gpr .r9 = BitVec.ofNat 64 v4 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) (BitVec.ofNat 64 v3)) ∧ Keep macRegs t t' from by
    refine WP.keep _ ?_ (by decide)
    mcrun [macWBody, j5, j6, j7, exec_load_d, exec_store_d,
      (hs.congr jk.wr).ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dM + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l8, l9, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l6, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l7, show dM + 8 * i + 8 = dM + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wm : word t.mem B (dM + 8 * i) = word s.mem B (dM + 8 * i) :=
      jout.word (by have := aM.outside hi; omega_arith) (by omega_arith)
    have k := macW_arith (t.gpr .r11).toNat (word t.mem B (dM + 8 * i)).toNat (word t.mem B (dA + 8 * i)).toNat
      (t.gpr .r9).toNat (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    simp only at k
    rw [lm, l9, wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dM i,
      wordsVal_succ_top s.mem B dA i, ← pow64_mul i]
    simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
    rw [← wa, ← wm, ← k11]
    rw [← k11] at jeq
    generalize 2 ^ (64 * i) = P at *
    grind

/-! ## The shift by 59 -/

/-- A word of the shift by 59: the top five bits of `x` and the low 59 of `y`. -/
theorem shr_arith (x y : BitVec 64) :
    (x >>> 59 + y <<< 5).toNat = x.toNat / 2 ^ 59 + 2 ^ 5 * (y.toNat % 2 ^ 59) := by
  have h1 : (x >>> 59).toNat = x.toNat / 2 ^ 59 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (y <<< 5).toNat = 2 ^ 5 * (y.toNat % 2 ^ 59) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have := y.isLt
    omega_arith
  rw [BitVec.toNat_add, h1, h2]
  have := x.isLt
  have : x.toNat / 2 ^ 59 < 2 ^ 5 := Nat.div_lt_of_lt_mul (by omega_using [])
  omega_arith

/-- The shift's invariant, a word on: `R + 2^(64 i) ⌊a / 2^59⌋ = ⌊A / 2^59⌋`
for `A` the first `i + 1` words, with `a` the last of them. -/
theorem shr_inv_step {R A a y i : Nat}
    (h : R + 2 ^ (64 * i) * (a / 2 ^ 59) = (A + 2 ^ (64 * i) * a) / 2 ^ 59) :
    R + 2 ^ (64 * i) * (a / 2 ^ 59 + 2 ^ 5 * (y % 2 ^ 59)) + 2 ^ (64 * (i + 1)) * (y / 2 ^ 59) =
      (A + 2 ^ (64 * i) * a + 2 ^ (64 * (i + 1)) * y) / 2 ^ 59 := by
  have e : 2 ^ (64 * (i + 1)) = 2 ^ 59 * (2 ^ (64 * i) * 2 ^ 5) := by
    rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 64 = 2 ^ 59 * 2 ^ 5 from rfl]; ac_rfl
  have hR : (A + 2 ^ (64 * i) * a + 2 ^ 59 * (2 ^ (64 * i) * 2 ^ 5) * y) / 2 ^ 59 =
      (A + 2 ^ (64 * i) * a) / 2 ^ 59 + 2 ^ (64 * i) * 2 ^ 5 * y := by
    rw [Nat.mul_assoc (2 ^ 59), Nat.add_mul_div_left _ _ (Nat.two_pow_pos 59)]
  rw [e, hR, ← h]
  have hy := Nat.mod_add_div y (2 ^ 59)
  have k : 2 ^ (64 * i) * 2 ^ 5 * y = 2 ^ (64 * i) * (2 ^ 5 * (y % 2 ^ 59)) +
      2 ^ 59 * (2 ^ (64 * i) * 2 ^ 5) * (y / 2 ^ 59) := by
    have : 2 ^ (64 * i) * 2 ^ 5 * y = 2 ^ (64 * i) * 2 ^ 5 * (y % 2 ^ 59 + 2 ^ 59 * (y / 2 ^ 59)) := by rw [hy]
    rw [this, Nat.mul_add]; ac_rfl
  rw [Nat.mul_add, k]
  omega_using []

/-! ## Signed accumulators -/

/-- `x` if `c`'s top bit is set, else 0: `(c >>> 63) x`. -/
theorem msb_mul (c x : BitVec 64) :
    ((c >>> 63) * x).toNat = if c.toNat < 2 ^ 63 then 0 else x.toNat := by
  have hc := c.isLt
  have e : (c >>> 63).toNat = if c.toNat < 2 ^ 63 then 0 else 1 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; split <;> omega_arith
  rw [BitVec.toNat_mul, e]
  split
  · simp
  · simp only [Nat.one_mul]; exact Nat.mod_eq_of_lt x.isLt

/-- A signed coefficient times an unsigned word: `mul`'s low word and
`mulhu`'s high word less the word where the coefficient is negative. -/
theorem smul_split (c x : BitVec 64) :
    ((c * x).toNat : Int) + 2 ^ 64 * ((c.toNat * x.toNat / 2 ^ 64 : Nat) - (((c >>> 63) * x).toNat : Int)) =
      c.toInt * x.toNat := by
  rw [BitVec.toNat_mul, BitVec.toInt_eq_toNat_cond, msb_mul]
  have hc := c.isLt
  by_cases h : c.toNat < 2 ^ 63
  · simp only [h, show 2 * c.toNat < 2 ^ 64 by omega_using [h], ↓reduceIte]
    rw [← Int.natCast_mul]
    generalize c.toNat * x.toNat = P
    omega_using []
  · simp only [h, show ¬ 2 * c.toNat < 2 ^ 64 by omega_using [h], ↓reduceIte]
    rw [Int.sub_mul, ← Int.natCast_mul]
    generalize c.toNat * x.toNat = P
    omega_using []

/-- The carry bit of a sum of two words. -/
theorem carry_bit (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (decide (2 ^ 64 ≤ a + b)).toNat = (a + b) / 2 ^ 64 := by
  by_cases h : 2 ^ 64 ≤ a + b
  · rw [decide_eq_true h, Bool.toNat_true]; omega_using [ha, hb, h]
  · rw [decide_eq_false h, Bool.toNat_false]; omega_using [h]

/-- A signed accumulator: the low word unsigned, the high signed. -/
def acc (lo hi : BitVec 64) : Int := lo.toNat + 2 ^ 64 * hi.toInt

/-- A term of an accumulator: plus a signed coefficient times a word, when
the sum fits; the carry of the low words by the carry bit. -/
theorem lin_term (c x lo hi : BitVec 64)
    (h1 : -2 ^ 127 ≤ acc lo hi + c.toInt * x.toNat) (h2 : acc lo hi + c.toInt * x.toNat < 2 ^ 127) :
    acc (BitVec.ofNat 64 (lo.toNat + (c * x).toNat))
        (BitVec.ofNat 64 (hi.toNat + (decide (2 ^ 64 ≤ lo.toNat + (c * x).toNat)).toNat) +
          BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) - (c >>> 63) * x) =
      acc lo hi + c.toInt * x.toNat := by
  have hs := smul_split c x
  unfold acc at *
  rw [← hs] at h1 h2 ⊢
  have hc := c.isLt; have hx := x.isLt
  have hP : c.toNat * x.toNat / 2 ^ 64 < 2 ^ 64 := by
    have := Nat.mul_lt_mul_of_lt_of_le hc (Nat.le_of_lt hx) (by decide : 0 < 2 ^ 64)
    exact Nat.div_lt_of_lt_mul this
  have hL := (c * x).isLt
  have hM := ((c >>> 63) * x).isLt
  have ht := lo.isLt; have ha := hi.isLt
  have vcy := carry_bit lo.toNat (c * x).toNat ht hL
  generalize (decide (2 ^ 64 ≤ lo.toNat + (c * x).toNat)).toNat = cy at vcy ⊢
  have na : (BitVec.ofNat 64 (hi.toNat + cy) + BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) -
      (c >>> 63) * x).toNat =
      (2 ^ 64 - ((c >>> 63) * x).toNat +
        ((hi.toNat + cy) % 2 ^ 64 + c.toNat * x.toNat / 2 ^ 64 % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  generalize BitVec.ofNat 64 (hi.toNat + cy) + BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) -
    (c >>> 63) * x = hi' at na ⊢
  have ia := BitVec.toInt_eq_toNat_cond hi
  have ia' := BitVec.toInt_eq_toNat_cond hi'
  rw [BitVec.toNat_ofNat]
  generalize c.toNat * x.toNat / 2 ^ 64 = H at *
  generalize (c * x).toNat = L at *
  generalize ((c >>> 63) * x).toNat = M at *
  generalize lo.toNat = T at *
  generalize hi.toNat = A at *
  generalize hi'.toNat = A' at *
  split at ia <;> split at ia' <;> omega_arith

/-- The accumulator shifted down a word: the high word's value. -/
theorem acc_shift (a : BitVec 64) : acc a (0#64 - a >>> 63) = a.toInt := by
  unfold acc
  have ha := a.isLt
  have e : (a >>> 63).toNat = if a.toNat < 2 ^ 63 then 0 else 1 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; split <;> omega_arith
  rw [BitVec.toInt_eq_toNat_cond a]
  by_cases h : a.toNat < 2 ^ 63
  · have h0 : a >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [e]; simp only [h, ↓reduceIte, BitVec.toNat_zero]
    have h2 : 2 * a.toNat < 2 ^ 64 := by omega_using [h]
    rw [h0]
    simp only [h2, ↓reduceIte]
    simp
  · have h1 : a >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [e]; simp only [h, ↓reduceIte]; rfl
    have h2 : ¬ 2 * a.toNat < 2 ^ 64 := by omega_using [h]
    rw [h1, show (0#64 - 1#64) = BitVec.allOnes 64 from rfl, BitVec.toInt_allOnes]
    simp only [h2, ↓reduceIte]
    omega_using []

/-- A coefficient of at most `2^61` times a word. -/
theorem smul_bound (c x : BitVec 64) (h1 : -2 ^ 61 ≤ c.toInt) (h2 : c.toInt ≤ 2 ^ 61) :
    -2 ^ 125 ≤ c.toInt * x.toNat ∧ c.toInt * x.toNat ≤ 2 ^ 125 := by
  have hx0 : (0 : Int) ≤ x.toNat := Int.natCast_nonneg _
  have hx1 : (x.toNat : Int) ≤ 2 ^ 64 := by have := x.isLt; omega_using []
  have a := Int.mul_le_mul_of_nonneg_right h2 hx0
  have b := Int.mul_le_mul_of_nonneg_right h1 hx0
  omega_using [a, b]

/-- `lin`'s invariant, a word on. -/
theorem lin_inv_step {W Ai Bi x1 x2 k : Nat} {u v a S0 : Int} {lo hi : BitVec 64}
    (jeq : (W : Int) + 2 ^ k * a = u * Ai + v * Bi + S0) (e2 : acc lo hi = a + u * x1 + v * x2) :
    ((W + 2 ^ k * lo.toNat : Nat) : Int) + 2 ^ (k + 64) * hi.toInt =
      u * ((Ai + 2 ^ k * x1 : Nat) : Int) + v * ((Bi + 2 ^ k * x2 : Nat) : Int) + S0 := by
  unfold acc at e2
  rw [Int.pow_add]
  push_cast
  generalize (2 : Int) ^ k = M at *
  have := congrArg (M * ·) e2
  grind

/-! ## `zerosW` -/

/-- `[o] := 0` over `m` words (`zerosW`), from `r0 = 0`. -/
theorem zerosW_ok {s : State} {B : Addr} {Z dO m : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h8 : s.gpr .r8 = BitVec.ofNat 64 m) (h0 : s.gpr .r0 = 0)
    (hm : 1 ≤ m) (hm' : m < 2 ^ 32) (hO : dO + 8 * m ≤ Z) :
    WP isa zerosW s fun t =>
      wordsVal t.mem B dO m = 0 ∧ Outside B dO (8 * m) s.mem t.mem ∧ Keep [.r5, .r8] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧ wordsVal t.mem B dO i = 0 ∧
      Keep [.r5, .r8] s t
  refine WP.mono (wp_countdown (body := .block ([.store .d .r0 .r5 0, .addi .r5 .r5 8, .subi .r8 .r8 1] : List Instr))
    (cnt := .r8) (N := m) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, Outside.refl _ _ _ _, rfl, Keep.refl _ _⟩ h8)
    fun t ⟨_, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have j0 : t.gpr .r0 = 0 := (jk.gpr _ (by decide)).trans h0
  have hst : WP isa (.block ([.store .d .r0 .r5 0, .addi .r5 .r5 8, .subi .r8 .r8 1] : List Instr)) t fun t' =>
      (t'.gpr .r5 = off B (dO + 8 * i + 8) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) (0 : BitVec 64)) ∧ Keep [.r5, .r8] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j5, j0, (hs.congr jk.wr).st (show dO + 8 * i + 8 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B (d := dO + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · rw [lm, wordsVal_write_top _ _ _ _ _ (by omega_arith), jeq]; rfl

/-! ## The fused passes' words -/

/-- The mask of a coefficient's sign, all ones where it is negative. -/
abbrev sgn (c : BitVec 64) : BitVec 64 := 0#64 - c >>> 63

theorem sgn_and (c x : BitVec 64) : sgn c &&& x = (c >>> 63) * x := by
  have hc := c.isLt
  by_cases h : c.toNat < 2 ^ 63
  · have e : c >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp only [BitVec.toNat_ofNat]; omega_using [h]
    rw [sgn, e]; simp
  · have e : c >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp only [BitVec.toNat_ofNat]; omega_using [h]
    rw [sgn, e, show (0#64 - 1#64) = BitVec.allOnes 64 from rfl, BitVec.allOnes_and, BitVec.one_mul]

/-- A term's low word: `lo + c x` by `addc`. -/
abbrev tlo (c x lo : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (lo.toNat + (c * x).toNat)

/-- A term's high word: `hi` with `mulhu`'s word and the carry by `adde`,
less `x` where `c` is negative. -/
abbrev thi (c x lo hi : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (hi.toNat + (BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64)).toNat +
    (decide (2 ^ 64 ≤ lo.toNat + (c * x).toNat)).toNat) - (sgn c &&& x)

/-- A term: the accumulator plus a signed coefficient times a word, when the
sum fits. -/
theorem term_acc (c x lo hi : BitVec 64)
    (h1 : -2 ^ 127 ≤ acc lo hi + c.toInt * x.toNat) (h2 : acc lo hi + c.toInt * x.toNat < 2 ^ 127) :
    acc (tlo c x lo) (thi c x lo hi) = acc lo hi + c.toInt * x.toNat := by
  have e : thi c x lo hi = BitVec.ofNat 64 (hi.toNat + (decide (2 ^ 64 ≤ lo.toNat + (c * x).toNat)).toNat) +
      BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) - (c >>> 63) * x := by
    rw [thi, sgn_and]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using []
  rw [e]
  exact lin_term c x lo hi h1 h2

/-- Two terms of an accumulator, `c₁ x + c₂ y`. -/
abbrev lo2 (c1 c2 x y lo : BitVec 64) : BitVec 64 := tlo c2 y (tlo c1 x lo)

abbrev hi2 (c1 c2 x y lo hi : BitVec 64) : BitVec 64 := thi c2 y (tlo c1 x lo) (thi c1 x lo hi)

/-- The two terms, when the accumulator is in the half range and the
coefficients at most `2^61`. -/
theorem acc_two (c1 c2 x y lo hi : BitVec 64)
    (h1 : -2 ^ 61 ≤ c1.toInt) (h2 : c1.toInt ≤ 2 ^ 61) (h3 : -2 ^ 61 ≤ c2.toInt) (h4 : c2.toInt ≤ 2 ^ 61)
    (hc1 : -2 ^ 63 ≤ acc lo hi) (hc2 : acc lo hi < 2 ^ 63) :
    acc (lo2 c1 c2 x y lo) (hi2 c1 c2 x y lo hi) = acc lo hi + c1.toInt * x.toNat + c2.toInt * y.toNat := by
  have b1 := smul_bound c1 x h1 h2
  have b2 := smul_bound c2 y h3 h4
  have e1 := term_acc c1 x lo hi (by omega_using [hc1, b1]) (by omega_using [hc2, b1])
  have e2 := term_acc c2 y _ _ (by rw [e1]; omega_using [hc1, b1, b2]) (by rw [e1]; omega_using [hc2, b1, b2])
  rw [e1] at e2
  exact e2

/-- One accumulator of the pass over `f` and `g`, after its words `0 … i`:
the low words `A + 2^(64 i) last` with the accumulator are `u F + v G`, and
the words stored, `R`, with `last`'s top five bits (`prev`), are the low
words shifted down by 59. -/
def FGAcc (u v : Int) (F G i R : Nat) (lo hi prev : BitVec 64) : Prop :=
  ∃ A : Nat, ∃ last : BitVec 64, A < 2 ^ (64 * i) ∧ prev = last >>> 59 ∧
    ((A + 2 ^ (64 * i) * last.toNat : Nat) : Int) + 2 ^ (64 * (i + 1)) * acc lo hi = u * F + v * G ∧
    R + 2 ^ (64 * i) * (last.toNat / 2 ^ 59) = (A + 2 ^ (64 * i) * last.toNat) / 2 ^ 59 ∧
    -2 ^ 63 ≤ acc lo hi ∧ acc lo hi < 2 ^ 63

/-- Word 0, from an empty accumulator. -/
theorem fg_init (c1 c2 x y lo hi : BitVec 64) (hl : lo = 0) (hh : hi = 0)
    (h1 : -2 ^ 61 ≤ c1.toInt) (h2 : c1.toInt ≤ 2 ^ 61) (h3 : -2 ^ 61 ≤ c2.toInt) (h4 : c2.toInt ≤ 2 ^ 61) :
    FGAcc c1.toInt c2.toInt x.toNat y.toNat 0 0 (hi2 c1 c2 x y lo hi) (0#64 - hi2 c1 c2 x y lo hi >>> 63)
      (lo2 c1 c2 x y lo >>> 59) := by
  have a0 : acc lo hi = 0 := by rw [hl, hh]; rfl
  have e := acc_two c1 c2 x y lo hi h1 h2 h3 h4 (by rw [a0]; decide) (by rw [a0]; decide)
  rw [a0, Int.zero_add] at e
  refine ⟨0, lo2 c1 c2 x y lo, by decide, rfl, ?_, by simp, ?_, ?_⟩
  · rw [acc_shift, show 64 * (0 + 1) = 64 from rfl, show 64 * 0 = 0 from rfl]
    unfold acc at e
    push_cast
    omega_using [e]
  · rw [acc_shift]; exact BitVec.le_toInt _
  · rw [acc_shift]; exact BitVec.toInt_lt

/-- A word `i + 1`: the accumulator's two terms, the word stored (the low
word's low 59 bits, then `prev`), and the next five bits. -/
theorem fg_step {c1 c2 : BitVec 64} {F G i R : Nat} {lo hi prev : BitVec 64} (x y : BitVec 64)
    (h1 : -2 ^ 61 ≤ c1.toInt) (h2 : c1.toInt ≤ 2 ^ 61) (h3 : -2 ^ 61 ≤ c2.toInt) (h4 : c2.toInt ≤ 2 ^ 61)
    (h : FGAcc c1.toInt c2.toInt F G i R lo hi prev) :
    FGAcc c1.toInt c2.toInt (F + 2 ^ (64 * (i + 1)) * x.toNat) (G + 2 ^ (64 * (i + 1)) * y.toNat) (i + 1)
      (R + 2 ^ (64 * i) * (lo2 c1 c2 x y lo <<< 5 + prev).toNat) (hi2 c1 c2 x y lo hi)
      (0#64 - hi2 c1 c2 x y lo hi >>> 63) (lo2 c1 c2 x y lo >>> 59) := by
  obtain ⟨A, last, hA, hp, hlin, hshr, hb1, hb2⟩ := h
  have e := acc_two c1 c2 x y lo hi h1 h2 h3 h4 hb1 hb2
  have hl := last.isLt
  refine ⟨A + 2 ^ (64 * i) * last.toNat, lo2 c1 c2 x y lo, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · have : A + 2 ^ (64 * i) * last.toNat < 2 ^ (64 * i) * 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (64 * i)) (show last.toNat + 1 ≤ 2 ^ 64 by omega_using [])
      rw [Nat.mul_add_one] at this; omega_using [hA, this]
    rwa [Nat.mul_succ, Nat.pow_add]
  · rw [acc_shift, show 64 * (i + 1 + 1) = 64 * (i + 1) + 64 by omega_using []]
    have := lin_inv_step (u := c1.toInt) (v := c2.toInt) (S0 := 0) (by rw [Int.add_zero]; exact hlin) e
    rwa [Int.add_zero] at this
  · rw [BitVec.add_comm, hp, shr_arith]
    exact shr_inv_step hshr
  · rw [acc_shift]; exact BitVec.le_toInt _
  · rw [acc_shift]; exact BitVec.toInt_lt

/-- `fmac`'s word: `k x + a + c`, by `addc` twice. -/
abbrev macS (k x a c : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((BitVec.ofNat 64 ((k * x).toNat + a.toNat)).toNat + c.toNat)

/-- `fmac`'s carry out: `mulhu`'s word with both carries, by `addze` twice. -/
abbrev macC (k x a c : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((BitVec.ofNat 64 ((BitVec.ofNat 64 (k.toNat * x.toNat / 2 ^ 64)).toNat +
    (decide (2 ^ 64 ≤ (k * x).toNat + a.toNat)).toNat)).toNat +
    (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((k * x).toNat + a.toNat)).toNat + c.toNat)).toNat)

theorem mac_word (k x a c : BitVec 64) :
    (macS k x a c).toNat + 2 ^ 64 * (macC k x a c).toNat = a.toNat + k.toNat * x.toNat + c.toNat := by
  have m := macW_arith k.toNat x.toNat a.toNat c.toNat k.isLt x.isLt a.isLt c.isLt
  simp only [macS, macC, BitVec.toNat_ofNat, BitVec.toNat_mul] at m ⊢
  have e : k.toNat * x.toNat / 2 ^ 64 % 2 ^ 64 = k.toNat * x.toNat / 2 ^ 64 := by
    have hkb : k.toNat * x.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := k.isLt; omega_using []) (by have := x.isLt; omega_using [])
    exact Nat.mod_eq_of_lt (by omega_using [m])
  rw [e] at m ⊢
  exact m

/-- One accumulator of the pass over `a` and `b`, after its words `0 … i`:
the low words `A` (the low one `w0`) with the accumulator are `u Da + v Db`,
and `k P` added to them is the words stored, `R`, and the carry `c`, a word
up (word 0 of the sum is zero). -/
def ABAcc (u v : Int) (k w0 : Nat) (Da Db P i R : Nat) (lo hi c : BitVec 64) : Prop :=
  ∃ A : Nat, A < 2 ^ (64 * (i + 1)) ∧ A % 2 ^ 64 = w0 ∧
    (A : Int) + 2 ^ (64 * (i + 1)) * acc lo hi = u * Da + v * Db ∧
    2 ^ 64 * (R + 2 ^ (64 * i) * c.toNat) = A + k * P ∧
    -2 ^ 63 ≤ acc lo hi ∧ acc lo hi < 2 ^ 63

/-- Word 0, from an empty accumulator and no carry: `k = t₀ iv` makes the
sum's word 0 zero, for `m₀ iv ≡ -1`. -/
theorem ab_init (c1 c2 x y m iv lo hi c : BitVec 64) (hl : lo = 0#64) (hh : hi = 0#64) (hc : c = 0#64)
    (h1 : -2 ^ 61 ≤ c1.toInt) (h2 : c1.toInt ≤ 2 ^ 61) (h3 : -2 ^ 61 ≤ c2.toInt) (h4 : c2.toInt ≤ 2 ^ 61)
    (hm : (m.toNat * iv.toNat + 1) % 2 ^ 64 = 0) :
    ABAcc c1.toInt c2.toInt (lo2 c1 c2 x y lo * iv).toNat (lo2 c1 c2 x y lo).toNat x.toNat y.toNat m.toNat 0 0
      (hi2 c1 c2 x y lo hi) (0#64 - hi2 c1 c2 x y lo hi >>> 63)
      (macC (lo2 c1 c2 x y lo * iv) m (lo2 c1 c2 x y lo) c) := by
  subst hl hh hc
  have e := acc_two c1 c2 x y 0#64 0#64 h1 h2 h3 h4 (by decide) (by decide)
  have a0 : acc 0#64 0#64 = 0 := rfl
  rw [a0, Int.zero_add] at e
  generalize hL : lo2 c1 c2 x y 0#64 = L at e ⊢
  have mw := mac_word (L * iv) m L 0#64
  have hz : (macS (L * iv) m L 0#64).toNat = 0 := by
    simp only [macS, BitVec.toNat_ofNat, BitVec.toNat_mul]
    rw [Nat.mod_mul_mod, Nat.zero_mod, Nat.add_zero, Nat.mod_add_mod,
      show L.toNat * iv.toNat * m.toNat + L.toNat = L.toNat * (m.toNat * iv.toNat + 1) by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm iv.toNat],
      Nat.mul_mod, hm, Nat.mul_zero, Nat.zero_mod]
  refine ⟨L.toNat, by have := L.isLt; simpa using this, Nat.mod_eq_of_lt L.isLt, ?_, ?_, ?_, ?_⟩
  · rw [acc_shift, show 64 * (0 + 1) = 64 from rfl]; unfold acc at e; omega_using [e]
  · rw [hz] at mw
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.add_zero] at mw ⊢
    omega_using [mw]
  · rw [acc_shift]; exact BitVec.le_toInt _
  · rw [acc_shift]; exact BitVec.toInt_lt

/-- A word `i + 1 < ν`: the accumulator's two terms, and `k m` added with the
carry, the word stored. -/
theorem ab_step {c1 c2 : BitVec 64} {k : BitVec 64} {w0 Da Db P i R : Nat} {lo hi c : BitVec 64}
    (x y m : BitVec 64)
    (h1 : -2 ^ 61 ≤ c1.toInt) (h2 : c1.toInt ≤ 2 ^ 61) (h3 : -2 ^ 61 ≤ c2.toInt) (h4 : c2.toInt ≤ 2 ^ 61)
    (h : ABAcc c1.toInt c2.toInt k.toNat w0 Da Db P i R lo hi c) :
    ABAcc c1.toInt c2.toInt k.toNat w0 (Da + 2 ^ (64 * (i + 1)) * x.toNat) (Db + 2 ^ (64 * (i + 1)) * y.toNat)
      (P + 2 ^ (64 * (i + 1)) * m.toNat) (i + 1)
      (R + 2 ^ (64 * i) * (macS k m (lo2 c1 c2 x y lo) c).toNat) (hi2 c1 c2 x y lo hi)
      (0#64 - hi2 c1 c2 x y lo hi >>> 63) (macC k m (lo2 c1 c2 x y lo) c) := by
  obtain ⟨A, hA, hw0, hlin, hmac, hb1, hb2⟩ := h
  have e := acc_two c1 c2 x y lo hi h1 h2 h3 h4 hb1 hb2
  have mw := mac_word k m (lo2 c1 c2 x y lo) c
  have hl := (lo2 c1 c2 x y lo).isLt
  refine ⟨A + 2 ^ (64 * (i + 1)) * (lo2 c1 c2 x y lo).toNat, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : A + 2 ^ (64 * (i + 1)) * (lo2 c1 c2 x y lo).toNat < 2 ^ (64 * (i + 1)) * 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (64 * (i + 1))) (show (lo2 c1 c2 x y lo).toNat + 1 ≤ 2 ^ 64 by omega_using [])
      rw [Nat.mul_add_one] at this; omega_using [hA, this]
    rwa [show 64 * (i + 1 + 1) = 64 * (i + 1) + 64 by omega_using [], Nat.pow_add]
  · rw [show 64 * (i + 1) = 64 * i + 64 by omega_using [], Nat.pow_add, Nat.mul_right_comm, Nat.add_mul_mod_self_right]
    exact hw0
  · rw [acc_shift, show 64 * (i + 1 + 1) = 64 * (i + 1) + 64 by omega_using []]
    have := lin_inv_step (u := c1.toInt) (v := c2.toInt) (S0 := 0) (W := A) (by rw [Int.add_zero]; exact hlin) e
    rwa [Int.add_zero] at this
  · have ep : 2 ^ (64 * (i + 1)) = 2 ^ 64 * 2 ^ (64 * i) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [ep]
    generalize 2 ^ (64 * i) = M at *
    generalize (macS k m (lo2 c1 c2 x y lo) c).toNat = S at *
    generalize (macC k m (lo2 c1 c2 x y lo) c).toNat = C at *
    generalize (lo2 c1 c2 x y lo).toNat = L at *
    generalize k.toNat = K at *
    have := congrArg (2 ^ 64 * M * ·) mw
    grind
  · rw [acc_shift]; exact BitVec.le_toInt _
  · rw [acc_shift]; exact BitVec.toInt_lt

/-! ## Two arrays written a word at a time -/

/-- Words `j` of two arrays written: the frame of both grows a word. -/
theorem outs_step2 {B : Addr} {m m' : Mem} {d e j : Nat} (h : Outs B [(d, 8 * j), (e, 8 * j)] m m')
    (v v' : BitVec 64) (hd : d + 8 * j + 8 ≤ 2 ^ 64) (he : e + 8 * j + 8 ≤ 2 ^ 64) :
    Outs B [(d, 8 * (j + 1)), (e, 8 * (j + 1))] m
      ((m'.writeW (off B (d + 8 * j)) v).writeW (off B (e + 8 * j)) v') := by
  intro x hx
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only at h1 h2
  rw [writeW_outside _ B v' he x (by omega_arith), writeW_outside _ B v hd x (by omega_arith)]
  exact h x fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith

/-- The words of the first of two arrays written, after a word of each. -/
theorem wv_step2 {B : Addr} (m : Mem) {d e j : Nat} (v v' : BitVec 64)
    (hd : d + 8 * j + 8 ≤ 2 ^ 64) (he : e + 8 * j + 8 ≤ 2 ^ 64)
    (hde : d + 8 * (j + 1) ≤ e + 8 * j ∨ e + 8 * j + 8 ≤ d) :
    wordsVal ((m.writeW (off B (d + 8 * j)) v).writeW (off B (e + 8 * j)) v') B d (j + 1) =
      wordsVal m B d j + 2 ^ (64 * j) * v.toNat := by
  rw [(writeW_outside _ B v' he).wordsVal (by omega_arith) (by omega_arith), wordsVal_write_top _ _ _ _ _ hd]

/-- The same, for the second array. -/
theorem wv_step2' {B : Addr} (m : Mem) {d e j : Nat} (v v' : BitVec 64)
    (he : e + 8 * j + 8 ≤ 2 ^ 64) :
    wordsVal ((m.writeW (off B (d + 8 * j)) v).writeW (off B (e + 8 * j)) v') B e (j + 1) =
      wordsVal (m.writeW (off B (d + 8 * j)) v) B e j + 2 ^ (64 * j) * v'.toNat :=
  wordsVal_write_top _ _ _ _ _ he

/-- The registers the pass over `f` and `g` changes. -/
abbrev fgRegs : List Reg := [.r0, .r3, .r5, .r6, .r8, .r12, .r22, .r23, .r24, .r25, .r26, .r27, .r28]

/-- The pass over `f` (at `dF`) and `g` (at `dG`), words `1 … n` (`countLoop
.r8 fgBody`), from word 0 in the accumulators: both accumulators' `FGAcc`
after word `n`, the words below it stored. -/
theorem fgLoop_ok {s : State} {B : Addr} {Z dF dG n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dF) (h6 : s.gpr .r6 = off B dG)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hF : dF + 8 * (n + 1) ≤ Z) (hG : dG + 8 * (n + 1) ≤ Z)
    (hFG : dF + 8 * (n + 1) ≤ dG ∨ dG + 8 * (n + 1) ≤ dF)
    (m18 : s.gpr .r18 = sgn (s.gpr .r14)) (m19 : s.gpr .r19 = sgn (s.gpr .r15))
    (m20 : s.gpr .r20 = sgn (s.gpr .r16)) (m21 : s.gpr .r21 = sgn (s.gpr .r17))
    (b1 : -2 ^ 61 ≤ (s.gpr .r14).toInt) (b2 : (s.gpr .r14).toInt ≤ 2 ^ 61)
    (b3 : -2 ^ 61 ≤ (s.gpr .r15).toInt) (b4 : (s.gpr .r15).toInt ≤ 2 ^ 61)
    (b5 : -2 ^ 61 ≤ (s.gpr .r16).toInt) (b6 : (s.gpr .r16).toInt ≤ 2 ^ 61)
    (b7 : -2 ^ 61 ≤ (s.gpr .r17).toInt) (b8 : (s.gpr .r17).toInt ≤ 2 ^ 61)
    (i1 : FGAcc (s.gpr .r14).toInt (s.gpr .r15).toInt (wordsVal s.mem B dF 1) (wordsVal s.mem B dG 1) 0 0
      (s.gpr .r22) (s.gpr .r23) (s.gpr .r28))
    (i2 : FGAcc (s.gpr .r16).toInt (s.gpr .r17).toInt (wordsVal s.mem B dF 1) (wordsVal s.mem B dG 1) 0 0
      (s.gpr .r24) (s.gpr .r25) (s.gpr .r12)) :
    WP isa (countLoop .r8 fgBody) s fun t =>
      FGAcc (s.gpr .r14).toInt (s.gpr .r15).toInt (wordsVal s.mem B dF (n + 1)) (wordsVal s.mem B dG (n + 1)) n
        (wordsVal t.mem B dF n) (t.gpr .r22) (t.gpr .r23) (t.gpr .r28) ∧
      FGAcc (s.gpr .r16).toInt (s.gpr .r17).toInt (wordsVal s.mem B dF (n + 1)) (wordsVal s.mem B dG (n + 1)) n
        (wordsVal t.mem B dG n) (t.gpr .r24) (t.gpr .r25) (t.gpr .r12) ∧
      t.gpr .r5 = off B (dF + 8 * n) ∧ t.gpr .r6 = off B (dG + 8 * n) ∧
      Outs B [(dF, 8 * n), (dG, 8 * n)] s.mem t.mem ∧ Keep fgRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r5 = off B (dF + 8 * j) ∧ t.gpr .r6 = off B (dG + 8 * j) ∧
      Outs B [(dF, 8 * j), (dG, 8 * j)] s.mem t.mem ∧
      FGAcc (s.gpr .r14).toInt (s.gpr .r15).toInt (wordsVal s.mem B dF (j + 1)) (wordsVal s.mem B dG (j + 1)) j
        (wordsVal t.mem B dF j) (t.gpr .r22) (t.gpr .r23) (t.gpr .r28) ∧
      FGAcc (s.gpr .r16).toInt (s.gpr .r17).toInt (wordsVal s.mem B dF (j + 1)) (wordsVal s.mem B dG (j + 1)) j
        (wordsVal t.mem B dG j) (t.gpr .r24) (t.gpr .r25) (t.gpr .r12) ∧
      Keep fgRegs s t
  refine WP.mono (wp_countdown (body := .block (fgBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun j hj t ⟨j5, j6, jout, ja, jb, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, Outs.refl _ _ _, by simpa [wordsVal] using i1,
      by simpa [wordsVal] using i2, Keep.refl _ _⟩ h8)
    fun t ⟨j5, j6, jout, ja, jb, jk⟩ => ⟨ja, jb, j5, j6, jout, jk⟩
  have hs' := hs.congr jk.wr
  have k14 : t.gpr .r14 = s.gpr .r14 := jk.gpr _ (by decide)
  have k15 : t.gpr .r15 = s.gpr .r15 := jk.gpr _ (by decide)
  have k16 : t.gpr .r16 = s.gpr .r16 := jk.gpr _ (by decide)
  have k17 : t.gpr .r17 = s.gpr .r17 := jk.gpr _ (by decide)
  have k18 : t.gpr .r18 = sgn (s.gpr .r14) := (jk.gpr _ (by decide)).trans m18
  have k19 : t.gpr .r19 = sgn (s.gpr .r15) := (jk.gpr _ (by decide)).trans m19
  have k20 : t.gpr .r20 = sgn (s.gpr .r16) := (jk.gpr _ (by decide)).trans m20
  have k21 : t.gpr .r21 = sgn (s.gpr .r17) := (jk.gpr _ (by decide)).trans m21
  have hst := (show WP isa (.block (fgBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      let x := word t.mem B (dF + 8 * j + 8)
      let y := word t.mem B (dG + 8 * j + 8)
      let l1 := lo2 (s.gpr .r14) (s.gpr .r15) x y (t.gpr .r22)
      let l2 := lo2 (s.gpr .r16) (s.gpr .r17) x y (t.gpr .r24)
      (t'.gpr .r5 = off B (dF + 8 * j + 8) ∧ t'.gpr .r6 = off B (dG + 8 * j + 8) ∧
        t'.gpr .r22 = hi2 (s.gpr .r14) (s.gpr .r15) x y (t.gpr .r22) (t.gpr .r23) ∧
        t'.gpr .r23 = 0#64 - hi2 (s.gpr .r14) (s.gpr .r15) x y (t.gpr .r22) (t.gpr .r23) >>> 63 ∧
        t'.gpr .r28 = l1 >>> 59 ∧
        t'.gpr .r24 = hi2 (s.gpr .r16) (s.gpr .r17) x y (t.gpr .r24) (t.gpr .r25) ∧
        t'.gpr .r25 = 0#64 - hi2 (s.gpr .r16) (s.gpr .r17) x y (t.gpr .r24) (t.gpr .r25) >>> 63 ∧
        t'.gpr .r12 = l2 >>> 59 ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = (t.mem.writeW (off B (dF + 8 * j)) (l1 <<< 5 + t.gpr .r28)).writeW (off B (dG + 8 * j))
          (l2 <<< 5 + t.gpr .r12)) ∧ Keep fgRegs t t' from by
    refine WP.keep _ ?_ (by decide)
    mcrun [fgBody, fterms, fterm, fout, fshift, hi2, lo2, tlo, thi, sgn, exec_adde, word, exec_load_d, exec_store_d,
      BitVec.add_zero, j5, j6, k14, k15, k16, k17, k18, k19, k20, k21,
      hs'.ld (show dF + 8 * j + 8 + 8 ≤ Z by omega_arith), hs'.ld (show dG + 8 * j + 8 + 8 ≤ Z by omega_arith),
      hs'.st (show dF + 8 * j + 8 ≤ Z by omega_arith), hs'.st (show dG + 8 * j + 8 ≤ Z by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l5, l6, l22, l23, l28, l24, l25, l12, l8, lm⟩, lk⟩ => ?_
  have wx : word t.mem B (dF + 8 * j + 8) = word s.mem B (dF + 8 * (j + 1)) := by
    rw [show dF + 8 * (j + 1) = dF + 8 * j + 8 by omega_arith]
    exact Outs.word jout (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  have wy : word t.mem B (dG + 8 * j + 8) = word s.mem B (dG + 8 * (j + 1)) := by
    rw [show dG + 8 * (j + 1) = dG + 8 * j + 8 by omega_arith]
    exact Outs.word jout (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  have eF : wordsVal s.mem B dF (j + 1 + 1) = wordsVal s.mem B dF (j + 1) +
      2 ^ (64 * (j + 1)) * (word t.mem B (dF + 8 * j + 8)).toNat := by rw [wx, wordsVal_succ_top]
  have eG : wordsVal s.mem B dG (j + 1 + 1) = wordsVal s.mem B dG (j + 1) +
      2 ^ (64 * (j + 1)) * (word t.mem B (dG + 8 * j + 8)).toNat := by rw [wy, wordsVal_succ_top]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dF + 8 * j + 8 = dF + 8 * (j + 1) by omega_arith]
  · rw [l6, show dG + 8 * j + 8 = dG + 8 * (j + 1) by omega_arith]
  · rw [lm]; exact outs_step2 jout _ _ (by omega_arith) (by omega_arith)
  · rw [l22, l23, l28, lm, eF, eG, wv_step2 _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact fg_step _ _ b1 b2 b3 b4 ja
  · rw [l24, l25, l12, lm, eF, eG, wv_step2' _ _ _ (by omega_arith),
      (writeW_outside _ B _ (d := dF + 8 * j) (by omega_arith)).wordsVal (by omega_arith) (by omega_arith)]
    exact fg_step _ _ b5 b6 b7 b8 jb

/-- The registers the pass over `a` and `b` changes. -/
abbrev abRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r11, .r22, .r23, .r24, .r25, .r26, .r27]

/-- The pass over `a` (at `dA`) and `b` (at `dB`) with `m` (at `dM`), words
`1 … n` (`countLoop .r8 abBody`), from word 0 in the accumulators and
carries: both accumulators' `ABAcc` after word `n`, the words below it
stored. -/
theorem abLoop_ok {s : State} {B : Addr} {Z dA dB dM n w1 w2 : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dA) (h6 : s.gpr .r6 = off B dB) (h7 : s.gpr .r7 = off B dM)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hA : dA + 8 * (n + 1) ≤ Z) (hB : dB + 8 * (n + 1) ≤ Z) (hM : dM + 8 * (n + 1) ≤ Z)
    (hAB : dA + 8 * (n + 1) ≤ dB ∨ dB + 8 * (n + 1) ≤ dA)
    (hAM : dA + 8 * (n + 1) ≤ dM ∨ dM + 8 * (n + 1) ≤ dA)
    (hBM : dB + 8 * (n + 1) ≤ dM ∨ dM + 8 * (n + 1) ≤ dB)
    (m18 : s.gpr .r18 = sgn (s.gpr .r14)) (m19 : s.gpr .r19 = sgn (s.gpr .r15))
    (m20 : s.gpr .r20 = sgn (s.gpr .r16)) (m21 : s.gpr .r21 = sgn (s.gpr .r17))
    (b1 : -2 ^ 61 ≤ (s.gpr .r14).toInt) (b2 : (s.gpr .r14).toInt ≤ 2 ^ 61)
    (b3 : -2 ^ 61 ≤ (s.gpr .r15).toInt) (b4 : (s.gpr .r15).toInt ≤ 2 ^ 61)
    (b5 : -2 ^ 61 ≤ (s.gpr .r16).toInt) (b6 : (s.gpr .r16).toInt ≤ 2 ^ 61)
    (b7 : -2 ^ 61 ≤ (s.gpr .r17).toInt) (b8 : (s.gpr .r17).toInt ≤ 2 ^ 61)
    (i1 : ABAcc (s.gpr .r14).toInt (s.gpr .r15).toInt (s.gpr .r28).toNat w1 (wordsVal s.mem B dA 1)
      (wordsVal s.mem B dB 1) (wordsVal s.mem B dM 1) 0 0 (s.gpr .r22) (s.gpr .r23) (s.gpr .r9))
    (i2 : ABAcc (s.gpr .r16).toInt (s.gpr .r17).toInt (s.gpr .r12).toNat w2 (wordsVal s.mem B dA 1)
      (wordsVal s.mem B dB 1) (wordsVal s.mem B dM 1) 0 0 (s.gpr .r24) (s.gpr .r25) (s.gpr .r11)) :
    WP isa (countLoop .r8 abBody) s fun t =>
      ABAcc (s.gpr .r14).toInt (s.gpr .r15).toInt (s.gpr .r28).toNat w1 (wordsVal s.mem B dA (n + 1))
        (wordsVal s.mem B dB (n + 1)) (wordsVal s.mem B dM (n + 1)) n (wordsVal t.mem B dA n)
        (t.gpr .r22) (t.gpr .r23) (t.gpr .r9) ∧
      ABAcc (s.gpr .r16).toInt (s.gpr .r17).toInt (s.gpr .r12).toNat w2 (wordsVal s.mem B dA (n + 1))
        (wordsVal s.mem B dB (n + 1)) (wordsVal s.mem B dM (n + 1)) n (wordsVal t.mem B dB n)
        (t.gpr .r24) (t.gpr .r25) (t.gpr .r11) ∧
      t.gpr .r5 = off B (dA + 8 * n) ∧ t.gpr .r6 = off B (dB + 8 * n) ∧ t.gpr .r7 = off B (dM + 8 * n) ∧
      Outs B [(dA, 8 * n), (dB, 8 * n)] s.mem t.mem ∧ Keep abRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r5 = off B (dA + 8 * j) ∧ t.gpr .r6 = off B (dB + 8 * j) ∧ t.gpr .r7 = off B (dM + 8 * j) ∧
      Outs B [(dA, 8 * j), (dB, 8 * j)] s.mem t.mem ∧
      ABAcc (s.gpr .r14).toInt (s.gpr .r15).toInt (s.gpr .r28).toNat w1 (wordsVal s.mem B dA (j + 1))
        (wordsVal s.mem B dB (j + 1)) (wordsVal s.mem B dM (j + 1)) j (wordsVal t.mem B dA j)
        (t.gpr .r22) (t.gpr .r23) (t.gpr .r9) ∧
      ABAcc (s.gpr .r16).toInt (s.gpr .r17).toInt (s.gpr .r12).toNat w2 (wordsVal s.mem B dA (j + 1))
        (wordsVal s.mem B dB (j + 1)) (wordsVal s.mem B dM (j + 1)) j (wordsVal t.mem B dB j)
        (t.gpr .r24) (t.gpr .r25) (t.gpr .r11) ∧
      Keep abRegs s t
  refine WP.mono (wp_countdown (body := .block (abBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun j hj t ⟨j5, j6, j7, jout, ja, jb, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl, Outs.refl _ _ _, by simpa [wordsVal] using i1,
      by simpa [wordsVal] using i2, Keep.refl _ _⟩ h8)
    fun t ⟨j5, j6, j7, jout, ja, jb, jk⟩ => ⟨ja, jb, j5, j6, j7, jout, jk⟩
  have hs' := hs.congr jk.wr
  have k14 : t.gpr .r14 = s.gpr .r14 := jk.gpr _ (by decide)
  have k15 : t.gpr .r15 = s.gpr .r15 := jk.gpr _ (by decide)
  have k16 : t.gpr .r16 = s.gpr .r16 := jk.gpr _ (by decide)
  have k17 : t.gpr .r17 = s.gpr .r17 := jk.gpr _ (by decide)
  have k18 : t.gpr .r18 = sgn (s.gpr .r14) := (jk.gpr _ (by decide)).trans m18
  have k19 : t.gpr .r19 = sgn (s.gpr .r15) := (jk.gpr _ (by decide)).trans m19
  have k20 : t.gpr .r20 = sgn (s.gpr .r16) := (jk.gpr _ (by decide)).trans m20
  have k21 : t.gpr .r21 = sgn (s.gpr .r17) := (jk.gpr _ (by decide)).trans m21
  have k28 : t.gpr .r28 = s.gpr .r28 := jk.gpr _ (by decide)
  have k12 : t.gpr .r12 = s.gpr .r12 := jk.gpr _ (by decide)
  have hst := (show WP isa (.block (abBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      let x := word t.mem B (dA + 8 * j + 8)
      let y := word t.mem B (dB + 8 * j + 8)
      let mw := word t.mem B (dM + 8 * j + 8)
      let l1 := lo2 (s.gpr .r14) (s.gpr .r15) x y (t.gpr .r22)
      let l2 := lo2 (s.gpr .r16) (s.gpr .r17) x y (t.gpr .r24)
      (t'.gpr .r5 = off B (dA + 8 * j + 8) ∧ t'.gpr .r6 = off B (dB + 8 * j + 8) ∧
        t'.gpr .r7 = off B (dM + 8 * j + 8) ∧
        t'.gpr .r22 = hi2 (s.gpr .r14) (s.gpr .r15) x y (t.gpr .r22) (t.gpr .r23) ∧
        t'.gpr .r23 = 0#64 - hi2 (s.gpr .r14) (s.gpr .r15) x y (t.gpr .r22) (t.gpr .r23) >>> 63 ∧
        t'.gpr .r9 = macC (s.gpr .r28) mw l1 (t.gpr .r9) ∧
        t'.gpr .r24 = hi2 (s.gpr .r16) (s.gpr .r17) x y (t.gpr .r24) (t.gpr .r25) ∧
        t'.gpr .r25 = 0#64 - hi2 (s.gpr .r16) (s.gpr .r17) x y (t.gpr .r24) (t.gpr .r25) >>> 63 ∧
        t'.gpr .r11 = macC (s.gpr .r12) mw l2 (t.gpr .r11) ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = (t.mem.writeW (off B (dA + 8 * j)) (macS (s.gpr .r28) mw l1 (t.gpr .r9))).writeW
          (off B (dB + 8 * j)) (macS (s.gpr .r12) mw l2 (t.gpr .r11))) ∧ Keep abRegs t t' from by
    refine WP.keep _ ?_ (by decide)
    mcrun [abBody, fterms, fterm, fmac, fshift, hi2, lo2, tlo, thi, sgn, macS, macC, exec_adde, word,
      exec_load_d, exec_store_d, BitVec.add_zero, j5, j6, j7, k14, k15, k16, k17, k18, k19, k20, k21, k28, k12,
      hs'.ld (show dA + 8 * j + 8 + 8 ≤ Z by omega_arith), hs'.ld (show dB + 8 * j + 8 + 8 ≤ Z by omega_arith),
      hs'.ld (show dM + 8 * j + 8 + 8 ≤ Z by omega_arith),
      hs'.st (show dA + 8 * j + 8 ≤ Z by omega_arith), hs'.st (show dB + 8 * j + 8 ≤ Z by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l22, l23, l9, l24, l25, l11, l8, lm⟩, lk⟩ => ?_
  have rd : ∀ d, (d = dA ∨ d = dB ∨ d = dM) → word t.mem B (d + 8 * j + 8) = word s.mem B (d + 8 * (j + 1)) := by
    intro d hd
    rw [show d + 8 * (j + 1) = d + 8 * j + 8 by omega_arith]
    exact Outs.word jout (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  have eA : wordsVal s.mem B dA (j + 1 + 1) = wordsVal s.mem B dA (j + 1) +
      2 ^ (64 * (j + 1)) * (word t.mem B (dA + 8 * j + 8)).toNat := by rw [rd _ (.inl rfl), wordsVal_succ_top]
  have eB : wordsVal s.mem B dB (j + 1 + 1) = wordsVal s.mem B dB (j + 1) +
      2 ^ (64 * (j + 1)) * (word t.mem B (dB + 8 * j + 8)).toNat := by rw [rd _ (.inr (.inl rfl)), wordsVal_succ_top]
  have eM : wordsVal s.mem B dM (j + 1 + 1) = wordsVal s.mem B dM (j + 1) +
      2 ^ (64 * (j + 1)) * (word t.mem B (dM + 8 * j + 8)).toNat := by rw [rd _ (.inr (.inr rfl)), wordsVal_succ_top]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dA + 8 * j + 8 = dA + 8 * (j + 1) by omega_arith]
  · rw [l6, show dB + 8 * j + 8 = dB + 8 * (j + 1) by omega_arith]
  · rw [l7, show dM + 8 * j + 8 = dM + 8 * (j + 1) by omega_arith]
  · rw [lm]; exact outs_step2 jout _ _ (by omega_arith) (by omega_arith)
  · rw [l22, l23, l9, lm, eA, eB, eM, wv_step2 _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact ab_step _ _ _ b1 b2 b3 b4 ja
  · rw [l24, l25, l11, lm, eA, eB, eM, wv_step2' _ _ _ (by omega_arith),
      (writeW_outside _ B _ (d := dA + 8 * j) (by omega_arith)).wordsVal (by omega_arith) (by omega_arith)]
    exact ab_step _ _ _ b5 b6 b7 b8 jb

/-- `abLoop_ok` when the count may be zero (`ν = 1`), behind its test. -/
theorem abLoop?_ok {s : State} {B : Addr} {Z dA dB dM n w1 w2 : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dA) (h6 : s.gpr .r6 = off B dB) (h7 : s.gpr .r7 = off B dM)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (hn' : n < 2 ^ 32)
    (hA : dA + 8 * (n + 1) ≤ Z) (hB : dB + 8 * (n + 1) ≤ Z) (hM : dM + 8 * (n + 1) ≤ Z)
    (hAB : dA + 8 * (n + 1) ≤ dB ∨ dB + 8 * (n + 1) ≤ dA)
    (hAM : dA + 8 * (n + 1) ≤ dM ∨ dM + 8 * (n + 1) ≤ dA)
    (hBM : dB + 8 * (n + 1) ≤ dM ∨ dM + 8 * (n + 1) ≤ dB)
    (m18 : s.gpr .r18 = sgn (s.gpr .r14)) (m19 : s.gpr .r19 = sgn (s.gpr .r15))
    (m20 : s.gpr .r20 = sgn (s.gpr .r16)) (m21 : s.gpr .r21 = sgn (s.gpr .r17))
    (b1 : -2 ^ 61 ≤ (s.gpr .r14).toInt) (b2 : (s.gpr .r14).toInt ≤ 2 ^ 61)
    (b3 : -2 ^ 61 ≤ (s.gpr .r15).toInt) (b4 : (s.gpr .r15).toInt ≤ 2 ^ 61)
    (b5 : -2 ^ 61 ≤ (s.gpr .r16).toInt) (b6 : (s.gpr .r16).toInt ≤ 2 ^ 61)
    (b7 : -2 ^ 61 ≤ (s.gpr .r17).toInt) (b8 : (s.gpr .r17).toInt ≤ 2 ^ 61)
    (i1 : ABAcc (s.gpr .r14).toInt (s.gpr .r15).toInt (s.gpr .r28).toNat w1 (wordsVal s.mem B dA 1)
      (wordsVal s.mem B dB 1) (wordsVal s.mem B dM 1) 0 0 (s.gpr .r22) (s.gpr .r23) (s.gpr .r9))
    (i2 : ABAcc (s.gpr .r16).toInt (s.gpr .r17).toInt (s.gpr .r12).toNat w2 (wordsVal s.mem B dA 1)
      (wordsVal s.mem B dB 1) (wordsVal s.mem B dM 1) 0 0 (s.gpr .r24) (s.gpr .r25) (s.gpr .r11)) :
    WP isa (.ite (.zero .d .r8) (.block []) (countLoop .r8 abBody)) s fun t =>
      ABAcc (s.gpr .r14).toInt (s.gpr .r15).toInt (s.gpr .r28).toNat w1 (wordsVal s.mem B dA (n + 1))
        (wordsVal s.mem B dB (n + 1)) (wordsVal s.mem B dM (n + 1)) n (wordsVal t.mem B dA n)
        (t.gpr .r22) (t.gpr .r23) (t.gpr .r9) ∧
      ABAcc (s.gpr .r16).toInt (s.gpr .r17).toInt (s.gpr .r12).toNat w2 (wordsVal s.mem B dA (n + 1))
        (wordsVal s.mem B dB (n + 1)) (wordsVal s.mem B dM (n + 1)) n (wordsVal t.mem B dB n)
        (t.gpr .r24) (t.gpr .r25) (t.gpr .r11) ∧
      t.gpr .r5 = off B (dA + 8 * n) ∧ t.gpr .r6 = off B (dB + 8 * n) ∧ t.gpr .r7 = off B (dM + 8 * n) ∧
      Outs B [(dA, 8 * n), (dB, 8 * n)] s.mem t.mem ∧ Keep abRegs s t := by
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega_arith) h8) (fun hz => ?_) (fun hz => ?_)
  · have hN : n = 0 := of_decide_eq_true hz
    subst hN
    exact WP.block_nil ⟨by simpa [wordsVal] using i1, by simpa [wordsVal] using i2, by rw [h5]; rfl,
      by rw [h6]; rfl, by rw [h7]; rfl, Outs.refl _ _ _, Keep.refl _ _⟩
  · exact abLoop_ok hs h5 h6 h7 h8 (Nat.pos_of_ne_zero (of_decide_eq_false hz)) hn' hA hB hM
      hAB hAM hBM m18 m19 m20 m21 b1 b2 b3 b4 b5 b6 b7 b8 i1 i2

end VG.Proof.Rsa.PPC64LE.Loops
