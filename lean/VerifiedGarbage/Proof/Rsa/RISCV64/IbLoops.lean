module

public import VerifiedGarbage.Impl.Rsa.RISCV64.InvBatch
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLoops
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.RangeCover

/-!
# The word loops of the batched inverse on RISC-V

Over `n` words of 64 bits at byte offsets of the working space (`Scr s B Z`),
multiples of 8, pointers in `t0`–`t2` and the count in `t3`, as
`KeyLoops.lean`'s (whose `subLoop_ok`, `selLoop_ok`, `copyLoop_ok` and
`zeroLoop_ok` the inverse also uses):

* `macLoop_ok`: `[o] := [a] + k [b]`, `k` in `a5`, the carry in and out in
  `t4`;
* `fgLoop_ok`: the pass over `f` and `g` (`fgBody`), two signed
  accumulators (`FGAcc`) whose low words, shifted by 59, are stored a word
  down, in place;
* `abLoop_ok` (`abLoop?_ok` when it may run no word): the pass over `a` and
  `b` (`abBody`), two signed accumulators with `k m` added to each low word
  by an unsigned carry (`ABAcc`), the sums stored a word down, in place.

The output may be an input, or come before it, or be apart from it
(`Ahead`): a word is read before any word at or after it is written.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.InvBatch (macBody fgBody fgHead fgOut fgShift term abBody abHead termR macW abShift)
open VG.Proof.Rsa.RISCV64.Loops (loopRegs Ahead out_step)

/-! ## `mac` -/

/-- A word of `a + k b + c`: the low word and the carry. -/
theorem mac_arith (k b a c : BitVec 64) :
    let lo := k * b + a
    let c1 : BitVec 64 := if lo < a then 1 else 0
    let s := lo + c
    let c2 : BitVec 64 := if s < c then 1 else 0
    s.toNat + 2 ^ 64 * (BitVec.ofNat 64 ((k.toNat * b.toNat) / 2 ^ 64) + c1 + c2).toNat =
      a.toNat + k.toNat * b.toNat + c.toNat := by
  intro lo c1 s c2
  have hk := k.isLt; have hb := b.isLt; have ha := a.isLt; have hc := c.isLt
  have hkb : k.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have vlo : lo.toNat = (k.toNat * b.toNat % 2 ^ 64 + a.toNat) % 2 ^ 64 := by
    simp only [lo, BitVec.toNat_add, BitVec.toNat_mul]
  have vs : s.toNat = (lo.toNat + c.toNat) % 2 ^ 64 := by simp only [s, BitVec.toNat_add]
  have vc1 : c1.toNat = (k.toNat * b.toNat % 2 ^ 64 + a.toNat) / 2 ^ 64 := by
    simp only [c1, BitVec.lt_def]; split <;> simp <;> omega
  have vc2 : c2.toNat = (lo.toNat + c.toNat) / 2 ^ 64 := by
    simp only [c2, BitVec.lt_def]; split <;> simp <;> omega
  have vhi : (BitVec.ofNat 64 ((k.toNat * b.toNat) / 2 ^ 64) + c1 + c2).toNat =
      k.toNat * b.toNat / 2 ^ 64 + c1.toNat + c2.toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : k.toNat * b.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by omega
    rw [vc1, vc2, vlo]
    omega
  rw [vhi, vs, vc1, vc2, vlo]
  generalize k.toNat * b.toNat = P at hkb ⊢
  omega

/-- `[o] := [a] + k [b]` over `n` words (`countLoop .t3 macBody`), from the
carry `c` in `t4`: the sum and the carry out. -/
theorem macLoop_ok {s : State} {B : Addr} {Z dO dA dM n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dO) (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dM)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hA8 : dA % 8 = 0) (hM8 : dM % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hA : dA + 8 * n ≤ Z) (hM : dM + 8 * n ≤ Z)
    (aA : Ahead dO dA n) (aM : Ahead dO dM n) :
    WP isa (countLoop .t3 macBody) s fun t =>
      wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .t4).toNat =
        wordsVal s.mem B dA n + (s.gpr .a5).toNat * wordsVal s.mem B dM n + (s.gpr .t4).toNat ∧
      t.gpr .t0 = off B (dO + 8 * n) ∧ Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ t.gpr .t1 = off B (dA + 8 * i) ∧ t.gpr .t2 = off B (dM + 8 * i) ∧
      Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .t4).toNat =
        wordsVal s.mem B dA i + (s.gpr .a5).toNat * wordsVal s.mem B dM i + (s.gpr .t4).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (macBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j2, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨j0, _, _, jout, jeq, jk⟩ => ⟨jeq, j0, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have k5 : t.gpr .a5 = s.gpr .a5 := jk.gpr (by decide)
  have hst := (show WP isa (.block (macBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      let bw := word t.mem B (dM + 8 * i)
      let aw := word t.mem B (dA + 8 * i)
      let lo := t.gpr .a5 * bw + aw
      let c1 : BitVec 64 := if lo < aw then 1 else 0
      let sw := lo + t.gpr .t4
      let c2 : BitVec 64 := if sw < t.gpr .t4 then 1 else 0
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t1 = off B (dA + 8 * i + 8) ∧
        t'.gpr .t2 = off B (dM + 8 * i + 8) ∧
        t'.gpr .t4 = BitVec.ofNat 64 ((t.gpr .a5).toNat * bw.toNat / 2 ^ 64) + c1 + c2 ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i)) sw) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [macBody, j0, j1, j2,
      hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith), hs'.ld (show dM + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dM + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    all_goals done)
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l4, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l1, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l2, show dM + 8 * i + 8 = dM + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dA + 8 * i) = word s.mem B (dA + 8 * i) :=
      jout.word (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wm : word t.mem B (dM + 8 * i) = word s.mem B (dM + 8 * i) :=
      jout.word (by have := aM.outside hi; omega_arith) (by omega_arith)
    have k := mac_arith (t.gpr .a5) (word t.mem B (dM + 8 * i)) (word t.mem B (dA + 8 * i)) (t.gpr .t4)
    simp only at k
    rw [lm, l4, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dM i,
      wordsVal_succ_top s.mem B dA i, Nat.mul_succ, Nat.pow_add, ← wa, ← wm, ← k5]
    rw [← k5] at jeq
    grind

/-! ## `shr` -/

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
  have : x.toNat / 2 ^ 59 < 2 ^ 5 := Nat.div_lt_of_lt_mul (by omega)
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
  omega

/-! ## `lin` -/

/-- A signed coefficient times an unsigned word: `mul`'s low word and
`mulhu`'s high word less the word where the coefficient is negative. -/
theorem smul_split (c x : BitVec 64) :
    ((c * x).toNat : Int) + 2 ^ 64 * ((c.toNat * x.toNat / 2 ^ 64 : Nat) - ((c.sshiftRight 63 &&& x).toNat : Int)) =
      c.toInt * x.toNat := by
  rw [BitVec.toNat_mul, BitVec.toInt_eq_toNat_cond]
  cases hm : c.msb
  · have hu : c.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide c; rw [hm] at this; simp at this; omega
    have h0 : c >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm, h0, BitVec.zero_and, ite_eq_left (by omega)]
    rw [← Int.natCast_mul]
    generalize c.toNat * x.toNat = P
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Int.natCast_zero, Int.sub_zero]
    omega
  · have hu : 2 ^ 63 ≤ c.toNat := by
      have := BitVec.msb_eq_decide c; rw [hm] at this; simp at this; omega
    have h0 : (~~~c) >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_true hm, h0, BitVec.not_zero, BitVec.allOnes_and,
      ite_eq_right (by omega), Int.sub_mul, ← Int.natCast_mul]
    generalize c.toNat * x.toNat = P
    omega

/-- The signed accumulator of `lin`: the low word unsigned, the high signed. -/
def acc (lo hi : BitVec 64) : Int := lo.toNat + 2 ^ 64 * hi.toInt

/-- `linTerm`: the accumulator plus a signed coefficient times a word, when
the sum fits. -/
theorem lin_term (c x t4 a4 : BitVec 64)
    (h1 : -2 ^ 127 ≤ acc t4 a4 + c.toInt * x.toNat) (h2 : acc t4 a4 + c.toInt * x.toNat < 2 ^ 127) :
    acc (t4 + c * x)
        (a4 + (if t4 + c * x < c * x then (1 : BitVec 64) else 0) + BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) -
          (c.sshiftRight 63 &&& x)) =
      acc t4 a4 + c.toInt * x.toNat := by
  have hs := smul_split c x
  unfold acc at *
  rw [← hs] at h1 h2 ⊢
  have hc := c.isLt; have hx := x.isLt
  have hP : c.toNat * x.toNat / 2 ^ 64 < 2 ^ 64 := by
    have := Nat.mul_lt_mul_of_lt_of_le hc (Nat.le_of_lt hx) (by decide : 0 < 2 ^ 64)
    exact Nat.div_lt_of_lt_mul this
  have hL := (c * x).isLt
  have hM := (c.sshiftRight 63 &&& x).isLt
  have ht := t4.isLt; have ha := a4.isLt
  have vcy : (if t4 + c * x < c * x then (1 : BitVec 64) else 0).toNat = (t4.toNat + (c * x).toNat) / 2 ^ 64 := by
    have e : (t4 + c * x).toNat = (t4.toNat + (c * x).toNat) % 2 ^ 64 := BitVec.toNat_add _ _
    by_cases hlt : t4 + c * x < c * x
    · rw [ite_eq_left hlt]; rw [BitVec.lt_def, e] at hlt
      generalize (c * x).toNat = L at *; simp; omega
    · rw [ite_eq_right hlt]; rw [BitVec.lt_def, e] at hlt
      generalize (c * x).toNat = L at *; simp; omega
  generalize (if t4 + c * x < c * x then (1 : BitVec 64) else 0) = cy at vcy ⊢
  have na : (a4 + cy + BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) - (c.sshiftRight 63 &&& x)).toNat =
      (2 ^ 64 - (c.sshiftRight 63 &&& x).toNat +
        ((a4.toNat + cy.toNat) % 2 ^ 64 + c.toNat * x.toNat / 2 ^ 64 % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
  generalize a4 + cy + BitVec.ofNat 64 (c.toNat * x.toNat / 2 ^ 64) - (c.sshiftRight 63 &&& x) = a4' at na ⊢
  have ia := BitVec.toInt_eq_toNat_cond a4
  have ia' := BitVec.toInt_eq_toNat_cond a4'
  rw [BitVec.toNat_add]
  rw [vcy] at na
  generalize c.toNat * x.toNat / 2 ^ 64 = H at *
  generalize (c * x).toNat = L at *
  generalize (c.sshiftRight 63 &&& x).toNat = M at *
  generalize t4.toNat = T at *
  generalize a4.toNat = A at *
  generalize a4'.toNat = A' at *
  split at ia <;> split at ia' <;> omega

/-- The accumulator shifted down a word: the high word's value. -/
theorem acc_shift (a : BitVec 64) : acc a (a.sshiftRight 63) = a.toInt := by
  unfold acc
  rw [BitVec.toInt_eq_toNat_cond a]
  cases hm : a.msb
  · have hu : a.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide a; rw [hm] at this; simp at this; omega
    have h0 : a >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm, h0, ite_eq_left (by omega)]; simp
  · have hu : 2 ^ 63 ≤ a.toNat := by
      have := BitVec.msb_eq_decide a; rw [hm] at this; simp at this; omega
    have h0 : (~~~a) >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_true hm, h0, BitVec.not_zero, ite_eq_right (by omega)]
    simp
    omega

/-- A coefficient of at most `2^61` times a word. -/
theorem smul_bound (c x : BitVec 64) (h1 : -2 ^ 61 ≤ c.toInt) (h2 : c.toInt ≤ 2 ^ 61) :
    -2 ^ 125 ≤ c.toInt * x.toNat ∧ c.toInt * x.toNat ≤ 2 ^ 125 := by
  have hx0 : (0 : Int) ≤ x.toNat := Int.natCast_nonneg _
  have hx1 : (x.toNat : Int) ≤ 2 ^ 64 := by have := x.isLt; omega
  have a := Int.mul_le_mul_of_nonneg_right h2 hx0
  have b := Int.mul_le_mul_of_nonneg_right h1 hx0
  omega

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


/-! ## The pass over `f` and `g` -/

/-- Two terms of an accumulator: `lo` and `hi` after `c₁ x + c₂ y` by `term`. -/
abbrev lo2 (c1 c2 x y lo : BitVec 64) : BitVec 64 := lo + c1 * x + c2 * y

abbrev hi2 (c1 c2 x y lo hi : BitVec 64) : BitVec 64 :=
  hi + (if lo + c1 * x < c1 * x then (1 : BitVec 64) else 0) + BitVec.ofNat 64 (c1.toNat * x.toNat / 2 ^ 64) -
      (c1.sshiftRight 63 &&& x) +
    (if lo + c1 * x + c2 * y < c2 * y then (1 : BitVec 64) else 0) +
    BitVec.ofNat 64 (c2.toNat * y.toNat / 2 ^ 64) - (c2.sshiftRight 63 &&& y)

/-- The two terms, when the accumulator is in the half range and the
coefficients at most `2^61`. -/
theorem acc_two (c1 c2 x y lo hi : BitVec 64)
    (h1 : -2 ^ 61 ≤ c1.toInt) (h2 : c1.toInt ≤ 2 ^ 61) (h3 : -2 ^ 61 ≤ c2.toInt) (h4 : c2.toInt ≤ 2 ^ 61)
    (hc1 : -2 ^ 63 ≤ acc lo hi) (hc2 : acc lo hi < 2 ^ 63) :
    acc (lo2 c1 c2 x y lo) (hi2 c1 c2 x y lo hi) = acc lo hi + c1.toInt * x.toNat + c2.toInt * y.toNat := by
  have b1 := smul_bound c1 x h1 h2
  have b2 := smul_bound c2 y h3 h4
  have e1 := lin_term c1 x lo hi (by omega) (by omega)
  have e2 := lin_term c2 y _ _ (by rw [e1]; omega) (by rw [e1]; omega)
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
    FGAcc c1.toInt c2.toInt x.toNat y.toNat 0 0 (hi2 c1 c2 x y lo hi) ((hi2 c1 c2 x y lo hi).sshiftRight 63)
      (lo2 c1 c2 x y lo >>> 59) := by
  have a0 : acc lo hi = 0 := by rw [hl, hh]; rfl
  have e := acc_two c1 c2 x y lo hi h1 h2 h3 h4 (by rw [a0]; decide) (by rw [a0]; decide)
  rw [a0, Int.zero_add] at e
  refine ⟨0, lo2 c1 c2 x y lo, by decide, rfl, ?_, by simp, ?_, ?_⟩
  · rw [acc_shift, show 64 * (0 + 1) = 64 from rfl, show 64 * 0 = 0 from rfl]
    unfold acc at e
    push_cast
    omega
  · rw [acc_shift]; exact BitVec.le_toInt _
  · rw [acc_shift]; exact BitVec.toInt_lt

/-- A word `i + 1`: the accumulator's two terms, the word stored (`prev` and
the low word's low 59 bits), and the next five bits. -/
theorem fg_step {c1 c2 : BitVec 64} {F G i R : Nat} {lo hi prev : BitVec 64} (x y : BitVec 64)
    (h1 : -2 ^ 61 ≤ c1.toInt) (h2 : c1.toInt ≤ 2 ^ 61) (h3 : -2 ^ 61 ≤ c2.toInt) (h4 : c2.toInt ≤ 2 ^ 61)
    (h : FGAcc c1.toInt c2.toInt F G i R lo hi prev) :
    FGAcc c1.toInt c2.toInt (F + 2 ^ (64 * (i + 1)) * x.toNat) (G + 2 ^ (64 * (i + 1)) * y.toNat) (i + 1)
      (R + 2 ^ (64 * i) * (prev + lo2 c1 c2 x y lo <<< 5).toNat) (hi2 c1 c2 x y lo hi)
      ((hi2 c1 c2 x y lo hi).sshiftRight 63) (lo2 c1 c2 x y lo >>> 59) := by
  obtain ⟨A, last, hA, hp, hlin, hshr, hb1, hb2⟩ := h
  have e := acc_two c1 c2 x y lo hi h1 h2 h3 h4 hb1 hb2
  have hl := last.isLt
  refine ⟨A + 2 ^ (64 * i) * last.toNat, lo2 c1 c2 x y lo, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · have : A + 2 ^ (64 * i) * last.toNat < 2 ^ (64 * i) * 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (64 * i)) (show last.toNat + 1 ≤ 2 ^ 64 by omega)
      rw [Nat.mul_add_one] at this; omega
    rwa [Nat.mul_succ, Nat.pow_add]
  · rw [acc_shift, show 64 * (i + 1 + 1) = 64 * (i + 1) + 64 by omega]
    have := lin_inv_step (u := c1.toInt) (v := c2.toInt) (S0 := 0) (by rw [Int.add_zero]; exact hlin) e
    rwa [Int.add_zero] at this
  · rw [hp, shr_arith]
    exact shr_inv_step hshr
  · rw [acc_shift]; exact BitVec.le_toInt _
  · rw [acc_shift]; exact BitVec.toInt_lt


/-! ## The pass over `a` and `b` -/

/-- `macW`'s word: `k x + a + c`. -/
abbrev macS (k x a c : BitVec 64) : BitVec 64 := k * x + a + c

/-- `macW`'s carry out. -/
abbrev macC (k x a c : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (k.toNat * x.toNat / 2 ^ 64) + (if k * x + a < a then (1 : BitVec 64) else 0) +
    (if k * x + a + c < c then (1 : BitVec 64) else 0)

theorem mac_word (k x a c : BitVec 64) :
    (macS k x a c).toNat + 2 ^ 64 * (macC k x a c).toNat = a.toNat + k.toNat * x.toNat + c.toNat :=
  mac_arith k x a c

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
      (hi2 c1 c2 x y lo hi) ((hi2 c1 c2 x y lo hi).sshiftRight 63)
      (macC (lo2 c1 c2 x y lo * iv) m (lo2 c1 c2 x y lo) c) := by
  subst hl hh hc
  have e := acc_two c1 c2 x y 0#64 0#64 h1 h2 h3 h4 (by decide) (by decide)
  have a0 : acc 0#64 0#64 = 0 := rfl
  rw [a0, Int.zero_add] at e
  generalize hL : lo2 c1 c2 x y 0#64 = L at e ⊢
  have mw := mac_word (L * iv) m L 0#64
  have hz : (macS (L * iv) m L 0#64).toNat = 0 := by
    simp only [macS, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_mul]
    have hl := L.isLt
    rw [Nat.mod_mul_mod, Nat.mod_add_mod,
      show L.toNat * iv.toNat * m.toNat + L.toNat = L.toNat * (m.toNat * iv.toNat + 1) by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm iv.toNat],
      Nat.mul_mod, hm, Nat.mul_zero, Nat.zero_mod]
  refine ⟨L.toNat, by have := L.isLt; simpa using this, Nat.mod_eq_of_lt L.isLt, ?_, ?_, ?_, ?_⟩
  · rw [acc_shift, show 64 * (0 + 1) = 64 from rfl]; unfold acc at e; omega
  · rw [hz] at mw
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.add_zero] at mw ⊢
    omega
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
      ((hi2 c1 c2 x y lo hi).sshiftRight 63) (macC k m (lo2 c1 c2 x y lo) c) := by
  obtain ⟨A, hA, hw0, hlin, hmac, hb1, hb2⟩ := h
  have e := acc_two c1 c2 x y lo hi h1 h2 h3 h4 hb1 hb2
  have mw := mac_word k m (lo2 c1 c2 x y lo) c
  have hl := (lo2 c1 c2 x y lo).isLt
  refine ⟨A + 2 ^ (64 * (i + 1)) * (lo2 c1 c2 x y lo).toNat, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : A + 2 ^ (64 * (i + 1)) * (lo2 c1 c2 x y lo).toNat < 2 ^ (64 * (i + 1)) * 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (64 * (i + 1))) (show (lo2 c1 c2 x y lo).toNat + 1 ≤ 2 ^ 64 by omega)
      rw [Nat.mul_add_one] at this; omega
    rwa [show 64 * (i + 1 + 1) = 64 * (i + 1) + 64 by omega, Nat.pow_add]
  · rw [show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add, Nat.mul_right_comm, Nat.add_mul_mod_self_right]
    exact hw0
  · rw [acc_shift, show 64 * (i + 1 + 1) = 64 * (i + 1) + 64 by omega]
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

/-- The words of one of two arrays written, after a word of each. -/
theorem wv_step2 {B : Addr} (m : Mem) {d e j : Nat} (v v' : BitVec 64)
    (hd : d + 8 * j + 8 ≤ 2 ^ 64) (he : e + 8 * j + 8 ≤ 2 ^ 64)
    (hde : d + 8 * (j + 1) ≤ e + 8 * j ∨ e + 8 * j + 8 ≤ d) :
    wordsVal ((m.writeW (off B (d + 8 * j)) v).writeW (off B (e + 8 * j)) v') B d (j + 1) =
      wordsVal m B d j + 2 ^ (64 * j) * v.toNat := by
  rw [(writeW_outside _ B v' he).wordsVal (by omega_arith) (by omega_arith), fin64_wordsVal_write_top _ _ _ _ _ hd]

/-- The same, for the second array. -/
theorem wv_step2' {B : Addr} (m : Mem) {d e j : Nat} (v v' : BitVec 64)
    (he : e + 8 * j + 8 ≤ 2 ^ 64) : 
    wordsVal ((m.writeW (off B (d + 8 * j)) v).writeW (off B (e + 8 * j)) v') B e (j + 1) =
      wordsVal (m.writeW (off B (d + 8 * j)) v) B e j + 2 ^ (64 * j) * v'.toNat :=
  fin64_wordsVal_write_top _ _ _ _ _ he

/-- The registers the pass over `f` and `g` changes. -/
abbrev fgRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a0, .a1, .a2, .a3]

/-- The pass over `f` (at `dF`) and `g` (at `dG`), words `1 … n` (`countLoop
.t3 fgBody`), from word 0 in the accumulators: both accumulators' `FGAcc`
after word `n`, the words below it stored. -/
theorem fgLoop_ok {s : State} {B : Addr} {Z dF dG n : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dF) (h1 : s.gpr .t1 = off B dG)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hF8 : dF % 8 = 0) (hG8 : dG % 8 = 0) (hF : dF + 8 * (n + 1) ≤ Z) (hG : dG + 8 * (n + 1) ≤ Z)
    (hFG : dF + 8 * (n + 1) ≤ dG ∨ dG + 8 * (n + 1) ≤ dF)
    (m3 : s.gpr .s3 = (s.gpr .a5).sshiftRight 63) (m4 : s.gpr .s4 = (s.gpr .a7).sshiftRight 63)
    (m5 : s.gpr .s5 = (s.gpr .s1).sshiftRight 63) (m6 : s.gpr .s6 = (s.gpr .s2).sshiftRight 63)
    (b1 : -2 ^ 61 ≤ (s.gpr .a5).toInt) (b2 : (s.gpr .a5).toInt ≤ 2 ^ 61)
    (b3 : -2 ^ 61 ≤ (s.gpr .a7).toInt) (b4 : (s.gpr .a7).toInt ≤ 2 ^ 61)
    (b5 : -2 ^ 61 ≤ (s.gpr .s1).toInt) (b6 : (s.gpr .s1).toInt ≤ 2 ^ 61)
    (b7 : -2 ^ 61 ≤ (s.gpr .s2).toInt) (b8 : (s.gpr .s2).toInt ≤ 2 ^ 61)
    (i1 : FGAcc (s.gpr .a5).toInt (s.gpr .a7).toInt (wordsVal s.mem B dF 1) (wordsVal s.mem B dG 1) 0 0
      (s.gpr .t4) (s.gpr .a4) (s.gpr .a2))
    (i2 : FGAcc (s.gpr .s1).toInt (s.gpr .s2).toInt (wordsVal s.mem B dF 1) (wordsVal s.mem B dG 1) 0 0
      (s.gpr .a0) (s.gpr .a1) (s.gpr .a3)) :
    WP isa (countLoop .t3 fgBody) s fun t =>
      FGAcc (s.gpr .a5).toInt (s.gpr .a7).toInt (wordsVal s.mem B dF (n + 1)) (wordsVal s.mem B dG (n + 1)) n
        (wordsVal t.mem B dF n) (t.gpr .t4) (t.gpr .a4) (t.gpr .a2) ∧
      FGAcc (s.gpr .s1).toInt (s.gpr .s2).toInt (wordsVal s.mem B dF (n + 1)) (wordsVal s.mem B dG (n + 1)) n
        (wordsVal t.mem B dG n) (t.gpr .a0) (t.gpr .a1) (t.gpr .a3) ∧
      t.gpr .t0 = off B (dF + 8 * n) ∧ t.gpr .t1 = off B (dG + 8 * n) ∧
      Outs B [(dF, 8 * n), (dG, 8 * n)] s.mem t.mem ∧ Keep fgRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .t0 = off B (dF + 8 * j) ∧ t.gpr .t1 = off B (dG + 8 * j) ∧
      Outs B [(dF, 8 * j), (dG, 8 * j)] s.mem t.mem ∧
      FGAcc (s.gpr .a5).toInt (s.gpr .a7).toInt (wordsVal s.mem B dF (j + 1)) (wordsVal s.mem B dG (j + 1)) j
        (wordsVal t.mem B dF j) (t.gpr .t4) (t.gpr .a4) (t.gpr .a2) ∧
      FGAcc (s.gpr .s1).toInt (s.gpr .s2).toInt (wordsVal s.mem B dF (j + 1)) (wordsVal s.mem B dG (j + 1)) j
        (wordsVal t.mem B dG j) (t.gpr .a0) (t.gpr .a1) (t.gpr .a3) ∧
      Keep fgRegs s t
  refine WP.mono (wp_countdown (body := .block (fgBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun j hj t ⟨j0, j1, jout, ja, jb, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, Outs.refl _ _ _, by simpa [wordsVal] using i1,
      by simpa [wordsVal] using i2, Keep.refl _ _⟩ h3)
    fun t ⟨j0, j1, jout, ja, jb, jk⟩ => ⟨ja, jb, j0, j1, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have k5 : t.gpr .a5 = s.gpr .a5 := jk.gpr (by decide)
  have k7 : t.gpr .a7 = s.gpr .a7 := jk.gpr (by decide)
  have ks1 : t.gpr .s1 = s.gpr .s1 := jk.gpr (by decide)
  have ks2 : t.gpr .s2 = s.gpr .s2 := jk.gpr (by decide)
  have ks3 : t.gpr .s3 = (s.gpr .a5).sshiftRight 63 := (jk.gpr (by decide)).trans m3
  have ks4 : t.gpr .s4 = (s.gpr .a7).sshiftRight 63 := (jk.gpr (by decide)).trans m4
  have ks5 : t.gpr .s5 = (s.gpr .s1).sshiftRight 63 := (jk.gpr (by decide)).trans m5
  have ks6 : t.gpr .s6 = (s.gpr .s2).sshiftRight 63 := (jk.gpr (by decide)).trans m6
  have hst := (show WP isa (.block (fgBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      let x := word t.mem B (dF + 8 * j + 8)
      let y := word t.mem B (dG + 8 * j + 8)
      let l1 := lo2 (s.gpr .a5) (s.gpr .a7) x y (t.gpr .t4)
      let l2 := lo2 (s.gpr .s1) (s.gpr .s2) x y (t.gpr .a0)
      (t'.gpr .t0 = off B (dF + 8 * j + 8) ∧ t'.gpr .t1 = off B (dG + 8 * j + 8) ∧
        t'.gpr .t4 = hi2 (s.gpr .a5) (s.gpr .a7) x y (t.gpr .t4) (t.gpr .a4) ∧
        t'.gpr .a4 = (hi2 (s.gpr .a5) (s.gpr .a7) x y (t.gpr .t4) (t.gpr .a4)).sshiftRight 63 ∧
        t'.gpr .a2 = l1 >>> 59 ∧
        t'.gpr .a0 = hi2 (s.gpr .s1) (s.gpr .s2) x y (t.gpr .a0) (t.gpr .a1) ∧
        t'.gpr .a1 = (hi2 (s.gpr .s1) (s.gpr .s2) x y (t.gpr .a0) (t.gpr .a1)).sshiftRight 63 ∧
        t'.gpr .a3 = l2 >>> 59 ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = (t.mem.writeW (off B (dF + 8 * j)) (t.gpr .a2 + l1 <<< 5)).writeW (off B (dG + 8 * j))
          (t.gpr .a3 + l2 <<< 5)) ∧ Keep fgRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fgBody, fgHead, fgOut, fgShift, term, hi2, lo2, BitVec.add_zero, j0, j1, k5, k7, ks1, ks2, ks3, ks4, ks5, ks6, off_add,
      hs'.ld (show dF + 8 * j + 8 + 8 ≤ Z by omega_arith), hs'.ld (show dG + 8 * j + 8 + 8 ≤ Z by omega_arith),
      hs'.st (show dF + 8 * j + 8 ≤ Z by omega_arith), hs'.st (show dG + 8 * j + 8 ≤ Z by omega_arith),
      hs'.al8 (show dF + 8 * j + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dG + 8 * j + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dF + 8 * j + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dG + 8 * j + 8 ≤ Z by omega_arith) (by omega_arith)]
    all_goals done)
  refine WP.mono hst fun t' ⟨⟨l0, l1, l4, la4, la2, la0, la1, la3, l3, lm⟩, lk⟩ => ?_
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
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dF + 8 * j + 8 = dF + 8 * (j + 1) by omega_arith]
  · rw [l1, show dG + 8 * j + 8 = dG + 8 * (j + 1) by omega_arith]
  · rw [lm]; exact outs_step2 jout _ _ (by omega_arith) (by omega_arith)
  · rw [l4, la4, la2, lm, eF, eG, wv_step2 _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact fg_step _ _ b1 b2 b3 b4 ja
  · rw [la0, la1, la3, lm, eF, eG, wv_step2' _ _ _ (by omega_arith), (writeW_outside _ B _ (d := dF + 8 * j) (by omega_arith)).wordsVal
      (by omega_arith) (by omega_arith)]
    exact fg_step _ _ b5 b6 b7 b8 jb

/-- The registers the pass over `a` and `b` changes. -/
abbrev abRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a0, .a1, .a6, .s0, .s6]

/-- The pass over `a` (at `dA`) and `b` (at `dB`) with `m` (at `dM`), words
`1 … n` (`countLoop .t3 abBody`), from word 0 in the accumulators and
carries: both accumulators' `ABAcc` after word `n`, the words below it
stored. -/
theorem abLoop_ok {s : State} {B : Addr} {Z dA dB dM n w1 w2 : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dA) (h1 : s.gpr .t1 = off B dB) (h2 : s.gpr .t2 = off B dM)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (hA : dA + 8 * (n + 1) ≤ Z) (hB : dB + 8 * (n + 1) ≤ Z) (hM : dM + 8 * (n + 1) ≤ Z)
    (hAB : dA + 8 * (n + 1) ≤ dB ∨ dB + 8 * (n + 1) ≤ dA)
    (hAM : dA + 8 * (n + 1) ≤ dM ∨ dM + 8 * (n + 1) ≤ dA)
    (hBM : dB + 8 * (n + 1) ≤ dM ∨ dM + 8 * (n + 1) ≤ dB)
    (m3 : s.gpr .s3 = (s.gpr .a5).sshiftRight 63) (m4 : s.gpr .s4 = (s.gpr .a7).sshiftRight 63)
    (m5 : s.gpr .s5 = (s.gpr .s1).sshiftRight 63)
    (b1 : -2 ^ 61 ≤ (s.gpr .a5).toInt) (b2 : (s.gpr .a5).toInt ≤ 2 ^ 61)
    (b3 : -2 ^ 61 ≤ (s.gpr .a7).toInt) (b4 : (s.gpr .a7).toInt ≤ 2 ^ 61)
    (b5 : -2 ^ 61 ≤ (s.gpr .s1).toInt) (b6 : (s.gpr .s1).toInt ≤ 2 ^ 61)
    (b7 : -2 ^ 61 ≤ (s.gpr .s2).toInt) (b8 : (s.gpr .s2).toInt ≤ 2 ^ 61)
    (i1 : ABAcc (s.gpr .a5).toInt (s.gpr .a7).toInt (s.gpr .a2).toNat w1 (wordsVal s.mem B dA 1)
      (wordsVal s.mem B dB 1) (wordsVal s.mem B dM 1) 0 0 (s.gpr .t4) (s.gpr .a4) (s.gpr .a6))
    (i2 : ABAcc (s.gpr .s1).toInt (s.gpr .s2).toInt (s.gpr .a3).toNat w2 (wordsVal s.mem B dA 1)
      (wordsVal s.mem B dB 1) (wordsVal s.mem B dM 1) 0 0 (s.gpr .a0) (s.gpr .a1) (s.gpr .s0)) :
    WP isa (countLoop .t3 abBody) s fun t =>
      ABAcc (s.gpr .a5).toInt (s.gpr .a7).toInt (s.gpr .a2).toNat w1 (wordsVal s.mem B dA (n + 1))
        (wordsVal s.mem B dB (n + 1)) (wordsVal s.mem B dM (n + 1)) n (wordsVal t.mem B dA n)
        (t.gpr .t4) (t.gpr .a4) (t.gpr .a6) ∧
      ABAcc (s.gpr .s1).toInt (s.gpr .s2).toInt (s.gpr .a3).toNat w2 (wordsVal s.mem B dA (n + 1))
        (wordsVal s.mem B dB (n + 1)) (wordsVal s.mem B dM (n + 1)) n (wordsVal t.mem B dB n)
        (t.gpr .a0) (t.gpr .a1) (t.gpr .s0) ∧
      t.gpr .t0 = off B (dA + 8 * n) ∧ t.gpr .t1 = off B (dB + 8 * n) ∧ t.gpr .t2 = off B (dM + 8 * n) ∧
      Outs B [(dA, 8 * n), (dB, 8 * n)] s.mem t.mem ∧ Keep abRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .t0 = off B (dA + 8 * j) ∧ t.gpr .t1 = off B (dB + 8 * j) ∧ t.gpr .t2 = off B (dM + 8 * j) ∧
      Outs B [(dA, 8 * j), (dB, 8 * j)] s.mem t.mem ∧
      ABAcc (s.gpr .a5).toInt (s.gpr .a7).toInt (s.gpr .a2).toNat w1 (wordsVal s.mem B dA (j + 1))
        (wordsVal s.mem B dB (j + 1)) (wordsVal s.mem B dM (j + 1)) j (wordsVal t.mem B dA j)
        (t.gpr .t4) (t.gpr .a4) (t.gpr .a6) ∧
      ABAcc (s.gpr .s1).toInt (s.gpr .s2).toInt (s.gpr .a3).toNat w2 (wordsVal s.mem B dA (j + 1))
        (wordsVal s.mem B dB (j + 1)) (wordsVal s.mem B dM (j + 1)) j (wordsVal t.mem B dB j)
        (t.gpr .a0) (t.gpr .a1) (t.gpr .s0) ∧
      Keep abRegs s t
  refine WP.mono (wp_countdown (body := .block (abBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun j hj t ⟨j0, j1, j2, jout, ja, jb, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, Outs.refl _ _ _, by simpa [wordsVal] using i1,
      by simpa [wordsVal] using i2, Keep.refl _ _⟩ h3)
    fun t ⟨j0, j1, j2, jout, ja, jb, jk⟩ => ⟨ja, jb, j0, j1, j2, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have k5 : t.gpr .a5 = s.gpr .a5 := jk.gpr (by decide)
  have k7 : t.gpr .a7 = s.gpr .a7 := jk.gpr (by decide)
  have ks1 : t.gpr .s1 = s.gpr .s1 := jk.gpr (by decide)
  have ks2 : t.gpr .s2 = s.gpr .s2 := jk.gpr (by decide)
  have ka2 : t.gpr .a2 = s.gpr .a2 := jk.gpr (by decide)
  have ka3 : t.gpr .a3 = s.gpr .a3 := jk.gpr (by decide)
  have ks3 : t.gpr .s3 = (s.gpr .a5).sshiftRight 63 := (jk.gpr (by decide)).trans m3
  have ks4 : t.gpr .s4 = (s.gpr .a7).sshiftRight 63 := (jk.gpr (by decide)).trans m4
  have ks5 : t.gpr .s5 = (s.gpr .s1).sshiftRight 63 := (jk.gpr (by decide)).trans m5
  have hst := (show WP isa (.block (abBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      let x := word t.mem B (dA + 8 * j + 8)
      let y := word t.mem B (dB + 8 * j + 8)
      let mw := word t.mem B (dM + 8 * j + 8)
      let l1 := lo2 (s.gpr .a5) (s.gpr .a7) x y (t.gpr .t4)
      let l2 := lo2 (s.gpr .s1) (s.gpr .s2) x y (t.gpr .a0)
      (t'.gpr .t0 = off B (dA + 8 * j + 8) ∧ t'.gpr .t1 = off B (dB + 8 * j + 8) ∧
        t'.gpr .t2 = off B (dM + 8 * j + 8) ∧
        t'.gpr .t4 = hi2 (s.gpr .a5) (s.gpr .a7) x y (t.gpr .t4) (t.gpr .a4) ∧
        t'.gpr .a4 = (hi2 (s.gpr .a5) (s.gpr .a7) x y (t.gpr .t4) (t.gpr .a4)).sshiftRight 63 ∧
        t'.gpr .a6 = macC (s.gpr .a2) mw l1 (t.gpr .a6) ∧
        t'.gpr .a0 = hi2 (s.gpr .s1) (s.gpr .s2) x y (t.gpr .a0) (t.gpr .a1) ∧
        t'.gpr .a1 = (hi2 (s.gpr .s1) (s.gpr .s2) x y (t.gpr .a0) (t.gpr .a1)).sshiftRight 63 ∧
        t'.gpr .s0 = macC (s.gpr .a3) mw l2 (t.gpr .s0) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = (t.mem.writeW (off B (dA + 8 * j)) (macS (s.gpr .a2) mw l1 (t.gpr .a6))).writeW
          (off B (dB + 8 * j)) (macS (s.gpr .a3) mw l2 (t.gpr .s0))) ∧ Keep abRegs t t' from by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [abBody, abHead, termR, macW, abShift, term, hi2, lo2, macS, macC, BitVec.add_zero, j0, j1, j2,
      k5, k7, ks1, ks2, ks3, ks4, ks5, ka2, ka3, off_add,
      hs'.ld (show dA + 8 * j + 8 + 8 ≤ Z by omega_arith), hs'.ld (show dB + 8 * j + 8 + 8 ≤ Z by omega_arith),
      hs'.ld (show dM + 8 * j + 8 + 8 ≤ Z by omega_arith),
      hs'.st (show dA + 8 * j + 8 ≤ Z by omega_arith), hs'.st (show dB + 8 * j + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * j + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dB + 8 * j + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dM + 8 * j + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dA + 8 * j + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dB + 8 * j + 8 ≤ Z by omega_arith) (by omega_arith)]
    all_goals done)
  refine WP.mono hst fun t' ⟨⟨l0, l1, l2, l4, la4, la6, la0, la1, ls0, l3, lm⟩, lk⟩ => ?_
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
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dA + 8 * j + 8 = dA + 8 * (j + 1) by omega_arith]
  · rw [l1, show dB + 8 * j + 8 = dB + 8 * (j + 1) by omega_arith]
  · rw [l2, show dM + 8 * j + 8 = dM + 8 * (j + 1) by omega_arith]
  · rw [lm]; exact outs_step2 jout _ _ (by omega_arith) (by omega_arith)
  · rw [l4, la4, la6, lm, eA, eB, eM, wv_step2 _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact ab_step _ _ _ b1 b2 b3 b4 ja
  · rw [la0, la1, ls0, lm, eA, eB, eM, wv_step2' _ _ _ (by omega_arith),
      (writeW_outside _ B _ (d := dA + 8 * j) (by omega_arith)).wordsVal (by omega_arith) (by omega_arith)]
    exact ab_step _ _ _ b5 b6 b7 b8 jb

/-- `abLoop_ok` when the count may be zero (`ν = 1`), behind its test. -/
theorem abLoop?_ok {s : State} {B : Addr} {Z dA dB dM n w1 w2 : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .t0 = off B dA) (h1 : s.gpr .t1 = off B dB) (h2 : s.gpr .t2 = off B dM)
    (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (hn' : n < 2 ^ 32)
    (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (hA : dA + 8 * (n + 1) ≤ Z) (hB : dB + 8 * (n + 1) ≤ Z) (hM : dM + 8 * (n + 1) ≤ Z)
    (hAB : dA + 8 * (n + 1) ≤ dB ∨ dB + 8 * (n + 1) ≤ dA)
    (hAM : dA + 8 * (n + 1) ≤ dM ∨ dM + 8 * (n + 1) ≤ dA)
    (hBM : dB + 8 * (n + 1) ≤ dM ∨ dM + 8 * (n + 1) ≤ dB)
    (m3 : s.gpr .s3 = (s.gpr .a5).sshiftRight 63) (m4 : s.gpr .s4 = (s.gpr .a7).sshiftRight 63)
    (m5 : s.gpr .s5 = (s.gpr .s1).sshiftRight 63)
    (b1 : -2 ^ 61 ≤ (s.gpr .a5).toInt) (b2 : (s.gpr .a5).toInt ≤ 2 ^ 61)
    (b3 : -2 ^ 61 ≤ (s.gpr .a7).toInt) (b4 : (s.gpr .a7).toInt ≤ 2 ^ 61)
    (b5 : -2 ^ 61 ≤ (s.gpr .s1).toInt) (b6 : (s.gpr .s1).toInt ≤ 2 ^ 61)
    (b7 : -2 ^ 61 ≤ (s.gpr .s2).toInt) (b8 : (s.gpr .s2).toInt ≤ 2 ^ 61)
    (i1 : ABAcc (s.gpr .a5).toInt (s.gpr .a7).toInt (s.gpr .a2).toNat w1 (wordsVal s.mem B dA 1)
      (wordsVal s.mem B dB 1) (wordsVal s.mem B dM 1) 0 0 (s.gpr .t4) (s.gpr .a4) (s.gpr .a6))
    (i2 : ABAcc (s.gpr .s1).toInt (s.gpr .s2).toInt (s.gpr .a3).toNat w2 (wordsVal s.mem B dA 1)
      (wordsVal s.mem B dB 1) (wordsVal s.mem B dM 1) 0 0 (s.gpr .a0) (s.gpr .a1) (s.gpr .s0)) :
    WP isa (.ite (.zero .t3) (.block []) (countLoop .t3 abBody)) s fun t =>
      ABAcc (s.gpr .a5).toInt (s.gpr .a7).toInt (s.gpr .a2).toNat w1 (wordsVal s.mem B dA (n + 1))
        (wordsVal s.mem B dB (n + 1)) (wordsVal s.mem B dM (n + 1)) n (wordsVal t.mem B dA n)
        (t.gpr .t4) (t.gpr .a4) (t.gpr .a6) ∧
      ABAcc (s.gpr .s1).toInt (s.gpr .s2).toInt (s.gpr .a3).toNat w2 (wordsVal s.mem B dA (n + 1))
        (wordsVal s.mem B dB (n + 1)) (wordsVal s.mem B dM (n + 1)) n (wordsVal t.mem B dB n)
        (t.gpr .a0) (t.gpr .a1) (t.gpr .s0) ∧
      t.gpr .t0 = off B (dA + 8 * n) ∧ t.gpr .t1 = off B (dB + 8 * n) ∧ t.gpr .t2 = off B (dM + 8 * n) ∧
      Outs B [(dA, 8 * n), (dB, 8 * n)] s.mem t.mem ∧ Keep abRegs s t := by
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega_arith) h3) (fun hz => ?_) (fun hz => ?_)
  · have hN : n = 0 := of_decide_eq_true hz
    subst hN
    exact WP.block_nil ⟨by simpa [wordsVal] using i1, by simpa [wordsVal] using i2, by rw [h0]; rfl,
      by rw [h1]; rfl, by rw [h2]; rfl, Outs.refl _ _ _, Keep.refl _ _⟩
  · exact abLoop_ok hs h0 h1 h2 h3 (Nat.pos_of_ne_zero (of_decide_eq_false hz)) hn' hA8 hB8 hM8 hA hB hM
      hAB hAM hBM m3 m4 m5 b1 b2 b3 b4 b5 b6 b7 b8 i1 i2

/-- A word of the first of two arrays, at or after the words written. -/
theorem outs2_word {B : Addr} {m m' : Mem} {d e j i : Nat} (h : Outs B [(d, 8 * j), (e, 8 * j)] m m')
    (hi : j ≤ i) (hsep : d + 8 * i + 8 ≤ e ∨ e + 8 * j ≤ d + 8 * i) (fit : d + 8 * i + 8 ≤ 2 ^ 64) :
    word m' B (d + 8 * i) = word m B (d + 8 * i) :=
  Outs.word h (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) fit

/-- The same, of the second array. -/
theorem outs2_word' {B : Addr} {m m' : Mem} {d e j i : Nat} (h : Outs B [(d, 8 * j), (e, 8 * j)] m m')
    (hi : j ≤ i) (hsep : e + 8 * i + 8 ≤ d ∨ d + 8 * j ≤ e + 8 * i) (fit : e + 8 * i + 8 ≤ 2 ^ 64) :
    word m' B (e + 8 * i) = word m B (e + 8 * i) :=
  Outs.word h (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) fit

end VG.Proof.Rsa.RISCV64.InvBatch
