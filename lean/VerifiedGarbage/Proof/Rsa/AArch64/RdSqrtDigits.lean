module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdRoot
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on AArch64: the square root's digits, `norm` and its tail

Each digit after the first (`digit_ok`, `digits_ok`) against `RdRoot`'s `DV`, `norm` (`norm_ok`), and
the square root as a whole (`sqrt_ok`): `⌊√X⌋` and whether `X` is a square.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Impl.Bignum.Public (sCnt)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Proof.Bignum.SqrtRem (IsDigit)
open VG.Spec.Rsa (isqrt)

theorem exec_sbc_x' {s : State} {d n m : Reg} :
    exec (.sbc .x d n m) s = some (s.write .x d (s.gpr n + ~~~s.gpr m + BitVec.ofNat 64 s.c.toNat)) := rfl

/-- A word of `2 s`, from `s`'s word `x` and the one below, `p`. -/
abbrev dbl (x p : BitVec 64) : BitVec 64 := x <<< 1 ||| p >>> 63

theorem dbl_toNat (x p : BitVec 64) : (dbl x p).toNat = 2 * x.toNat % 2 ^ 64 + p.toNat / 2 ^ 63 := by
  have hp := p.isLt
  have h1 : (x <<< 1).toNat = 2 * x.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega_using []
  have h2 : (p >>> 63).toNat = p.toNat / 2 ^ 63 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd := sq_and_shl_small x (p >>> 63) 1 (by rw [h2]; omega_using [])
  unfold dbl
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
  omega_using []

/-- `msBody`'s low word: `q D + c`. -/
abbrev msLo (q D c : BitVec 64) : BitVec 64 := q * D + c + BitVec.ofNat 64 false.toNat

/-- `msBody`'s word: `x - (q D + c)`. -/
abbrev msW (q D c x : BitVec 64) : BitVec 64 := x + ~~~(msLo q D c) + BitVec.ofNat 64 true.toNat

/-- `msBody`'s carry: `⌊q D / 2^64⌋`, the addition's carry and the subtraction's borrow. -/
abbrev msC (q D c x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (q.toNat * D.toNat / 2 ^ 64) + 0 +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (q * D).toNat + c.toNat + false.toNat)).toNat -
    (0 + ~~~0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ x.toNat + (~~~(msLo q D c)).toNat + true.toNat)).toNat)

theorem msw_arith (q D c x : BitVec 64) :
    (msW q D c x).toNat + q.toNat * D.toNat + c.toNat = x.toNat + 2 ^ 64 * (msC q D c x).toNat := by
  have hq := q.isLt; have hd := D.isLt; have hx := x.isLt; have hc := c.isLt
  have hP : q.toNat * D.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_using []) (by omega_using [])
  have hP2 : q.toNat * D.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by decide)]; omega_using [hP]
  have m1 : (q * D).toNat = q.toNat * D.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  have l1 : (msLo q D c).toNat = (q.toNat * D.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64 := by
    simp only [msLo, BitVec.toNat_add, m1, BitVec.toNat_ofNat, Bool.toNat_false]; omega_using []
  have n1 : (~~~(msLo q D c)).toNat = 2 ^ 64 - 1 - (msLo q D c).toNat := by rw [BitVec.toNat_not]
  have w : (msW q D c x).toNat = (x.toNat + (2 ^ 64 - 1 - (msLo q D c).toNat) + 1) % 2 ^ 64 := by
    simp only [msW, BitVec.toNat_add, n1, BitVec.toNat_ofNat, Bool.toNat_true]; omega_using []
  have k : (msC q D c x).toNat = (q.toNat * D.toNat / 2 ^ 64 +
      (decide (2 ^ 64 ≤ (q * D).toNat + c.toNat + false.toNat)).toNat + 1 -
      (decide (2 ^ 64 ≤ x.toNat + (~~~(msLo q D c)).toNat + true.toNat)).toNat) % 2 ^ 64 := by
    unfold msC
    generalize decide (2 ^ 64 ≤ (q * D).toNat + c.toNat + false.toNat) = b1
    generalize decide (2 ^ 64 ≤ x.toNat + (~~~(msLo q D c)).toNat + true.toNat) = b2
    have n0 : (~~~(0 : BitVec 64)).toNat = 2 ^ 64 - 1 := rfl
    cases b1 <;> cases b2 <;>
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, n0, Bool.toNat_true, Bool.toNat_false,
        show (0 : BitVec 64).toNat = 0 from rfl] <;> omega_using []
  rw [w, k, l1, n1, l1, m1]
  simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
  by_cases c1 : 2 ^ 64 ≤ q.toNat * D.toNat % 2 ^ 64 + c.toNat <;>
    by_cases c2 : 2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - (q.toNat * D.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64) + 1 <;>
    simp only [c1, c2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_using [hP, c1, c2]

/-- `corBody`'s word: `x + c + E`, and its carry. -/
abbrev corW (c E x : BitVec 64) : BitVec 64 :=
  x + c + BitVec.ofNat 64 false.toNat + E + BitVec.ofNat 64 false.toNat
abbrev corC (c E x : BitVec 64) : BitVec 64 :=
  0 + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ x.toNat + c.toNat + false.toNat)).toNat + 0 +
    BitVec.ofNat 64 (decide (2 ^ 64 ≤ (x + c + BitVec.ofNat 64 false.toNat).toNat + E.toNat + false.toNat)).toNat

theorem corw_arith (c E x : BitVec 64) :
    (corW c E x).toNat + 2 ^ 64 * (corC c E x).toNat = x.toNat + c.toNat + E.toNat := by
  have hx := x.isLt; have hc := c.isLt; have he := E.isLt
  have a1 : (x + c + BitVec.ofNat 64 false.toNat).toNat = (x.toNat + c.toNat) % 2 ^ 64 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat_false]; omega_using []
  have w : (corW c E x).toNat = ((x.toNat + c.toNat) % 2 ^ 64 + E.toNat) % 2 ^ 64 := by
    unfold corW; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat_false]; omega_using []
  have k : (corC c E x).toNat = (decide (2 ^ 64 ≤ x.toNat + c.toNat + false.toNat)).toNat +
      (decide (2 ^ 64 ≤ (x + c + BitVec.ofNat 64 false.toNat).toNat + E.toNat + false.toNat)).toNat := by
    unfold corC
    generalize decide (2 ^ 64 ≤ x.toNat + c.toNat + false.toNat) = b1
    generalize decide (2 ^ 64 ≤ (x + c + BitVec.ofNat 64 false.toNat).toNat + E.toNat + false.toNat) = b2
    cases b1 <;> cases b2 <;> rfl
  rw [w, k, a1]
  simp only [Bool.toNat_false, Nat.add_zero]
  by_cases c1 : 2 ^ 64 ≤ x.toNat + c.toNat <;> by_cases c2 : 2 ^ 64 ≤ (x.toNat + c.toNat) % 2 ^ 64 + E.toNat <;>
    simp only [c1, c2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_using [c1, c2]

theorem and_mask_toNat' (x : BitVec 64) (b : Bool) : (x &&& mask b).toNat = b.toNat * x.toNat := by
  cases b
  · simp [mask]
  · simp only [mask, Bool.toNat_true, Nat.one_mul]
    rw [show (0 : BitVec 64) - BitVec.setWidth 64 (BitVec.ofBool true) = BitVec.allOnes 64 from by decide,
      BitVec.and_allOnes]

theorem out_step {s m : Mem} {B : Addr} {dO i : Nat} (v : BitVec 64) (h : Outside B dO (8 * i) s m)
    (hb : dO + 8 * i + 8 ≤ 2 ^ 64) : Outside B dO (8 * (i + 1)) s (m.writeW (off B (dO + 8 * i)) v) := by
  intro x hx
  rw [writeW_outside m B v hb x (by omega_using [hx])]
  exact h x (by omega_using [hx])

abbrev msRegs : List Reg := [.x2, .x3, .x4, .x5, .x6, .x13, .x14, .x16, .x17]

/-- `countLoop .x14 msBody`: the `n` words at `x16` less `q (2 [s]) + c`, `q` in `x1`, `c` in `x13`, for the
`n` words `[s]` at `x17` and `x2 = 0` (no bit below): the carry out in `x13`, and the bit of `2 [s]` past its
`n` words, from `x2`, its top word. -/
theorem msLoop_ok {s : State} {B : Addr} {Z dO dS n : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B dO) (h17 : s.gpr .x17 = off B dS) (h14 : s.gpr .x14 = BitVec.ofNat 64 n)
    (h2 : s.gpr .x2 = 0) (h7 : s.gpr .x7 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO : dO + 8 * n ≤ Z) (hS : dS + 8 * n ≤ Z) (hd : dS + 8 * n ≤ dO ∨ dO + 8 * n ≤ dS) :
    WP isa (countLoop .x14 msBody) s fun t =>
      wv t.mem B dO n + (s.gpr .x1).toNat * (2 * wv s.mem B dS n) + (s.gpr .x13).toNat =
        wv s.mem B dO n + 2 ^ (64 * n) * ((t.gpr .x13).toNat + (s.gpr .x1).toNat * ((t.gpr .x2).toNat / 2 ^ 63)) ∧
      t.gpr .x2 = word s.mem B (dS + 8 * (n - 1)) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep msRegs s t ∧ t.gpr .x16 = off B (dO + 8 * n) ∧
      t.gpr .x17 = off B (dS + 8 * n) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .x16 = off B (dO + 8 * i) ∧ t.gpr .x17 = off B (dS + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wv t.mem B dO i + (s.gpr .x1).toNat * (2 * wv s.mem B dS i) + (s.gpr .x13).toNat =
        wv s.mem B dO i + 2 ^ (64 * i) * ((t.gpr .x13).toNat + (s.gpr .x1).toNat * ((t.gpr .x2).toNat / 2 ^ 63)) ∧
      (0 < i → t.gpr .x2 = word s.mem B (dS + 8 * (i - 1))) ∧ Keep msRegs s t
  refine WP.mono (wp_countdown (body := .block (msBody ++ ([.subImm .x .x14 .x14 1] : List Instr)))
    (cnt := .x14) (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv
    (fun i hi t ⟨j16, j17, jout, jeq, jt2, jk⟩ hc => ?_)
    ⟨by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, by simp [wv, h2], fun h => absurd h (by decide),
      Keep.refl _ _⟩ h14)
    fun t ⟨j16, j17, jout, jeq, jt2, jk⟩ => ⟨jeq, jt2 (by omega_using [hn]), jout, jk, j16, j17⟩
  have hs' := hs.congr jk.wr
  have t1 : t.gpr .x1 = s.gpr .x1 := jk.gpr .x1 (by decide)
  have t7 : t.gpr .x7 = 0 := (jk.gpr .x7 (by decide)).trans h7
  have hst : WP isa (.block (msBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      (t'.gpr .x16 = off B (dO + 8 * i + 8) ∧ t'.gpr .x17 = off B (dS + 8 * i + 8) ∧
        t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 ∧ t'.gpr .x2 = word t.mem B (dS + 8 * i) ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (msW (t.gpr .x1) (dbl (word t.mem B (dS + 8 * i)) (t.gpr .x2)) (t.gpr .x13) (word t.mem B (dO + 8 * i))) ∧
        t'.gpr .x13 = msC (t.gpr .x1) (dbl (word t.mem B (dS + 8 * i)) (t.gpr .x2)) (t.gpr .x13)
          (word t.mem B (dO + 8 * i))) ∧
      Keep msRegs t t' := by
    refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
    unfold msBody twoS
    brun [exec_sbc_x', t7, j16, j17, off_add, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_using [hO, hi]),
      hs'.ld (show dS + 8 * i + 8 ≤ Z by omega_using [hS, hi]), hs'.st (show dO + 8 * i + 8 ≤ Z by omega_using [hO, hi])]
  refine WP.mono hst fun t' ⟨⟨l16, l17, l14, l2, lm, l13⟩, lk⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, fun _ => ?_, (jk.trans lk).mono (by decide)⟩, l14⟩
  · rw [l16, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_using []]
  · rw [l17, show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_using []]
  · rw [lm]; exact out_step _ jout (by omega_using [hO, hnw, hi])
  · have wo : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_using []) (by omega_using [hO, hnw, hi])
    have wx : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) := jout.word (by omega_using [hd, hi]) (by omega_using [hS, hnw, hi])
    have k := msw_arith (t.gpr .x1) (dbl (word t.mem B (dS + 8 * i)) (t.gpr .x2)) (t.gpr .x13)
      (word t.mem B (dO + 8 * i))
    have dv := dbl_toNat (word t.mem B (dS + 8 * i)) (t.gpr .x2)
    rw [← l13] at k
    rw [lm, wv_writeW_top _ _ _ _ _ (by omega_using [hO, hnw, hi]), wv_top s.mem B dO i, wv_top s.mem B dS i, l2, Nat.mul_succ,
      Nat.pow_add]
    rw [wo, wx, t1] at k
    rw [wx] at dv
    rw [wo, wx, t1]
    have hx := (word s.mem B (dS + 8 * i)).isLt
    generalize (word s.mem B (dS + 8 * i)).toNat = X at *
    generalize (t.gpr .x2).toNat / 2 ^ 63 = tb at *
    generalize (dbl (word s.mem B (dS + 8 * i)) (t.gpr .x2)).toNat = D at *
    generalize (s.gpr .x1).toNat = q at *
    generalize (word s.mem B (dO + 8 * i)).toNat = xo at *
    generalize (msW (s.gpr .x1) (dbl (word s.mem B (dS + 8 * i)) (t.gpr .x2)) (t.gpr .x13)
      (word s.mem B (dO + 8 * i))).toNat = x' at *
    generalize (t'.gpr .x13).toNat = c' at *
    generalize (t.gpr .x13).toNat = c at *
    generalize 2 ^ (64 * i) = P at *
    have e2 : 2 * X + tb = D + 2 ^ 64 * (X / 2 ^ 63) := by omega_using [dv]
    have e3 : q * (2 * X) + q * tb = q * D + 2 ^ 64 * (q * (X / 2 ^ 63)) := by
      rw [← Nat.mul_add, e2, Nat.mul_add, Nat.mul_left_comm]
    grind
  · rw [l2, show i + 1 - 1 = i by omega_using []]
    exact jout.word (by omega_using [hd, hi]) (by omega_using [hS, hnw, hi])

abbrev corRegs : List Reg := [.x2, .x3, .x4, .x5, .x13, .x14, .x16, .x17]

/-- `countLoop .x14 corBody`: the `n` words at `x16` plus `b (2 [s]) + c`, `b` a bit (`x15` its mask), `c` in
`x13`, for the `n` words `[s]` at `x17` and `x2 = 0`: the carry out in `x13`, and the bit of `2 [s]` past its
`n` words, from `x2`, its top word. -/
theorem corLoop_ok {s : State} {B : Addr} {Z dO dS n : Nat} {b : Bool} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B dO) (h17 : s.gpr .x17 = off B dS) (h14 : s.gpr .x14 = BitVec.ofNat 64 n)
    (h2 : s.gpr .x2 = 0) (h7 : s.gpr .x7 = 0) (h15 : s.gpr .x15 = mask b) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO : dO + 8 * n ≤ Z) (hS : dS + 8 * n ≤ Z) (hd : dS + 8 * n ≤ dO ∨ dO + 8 * n ≤ dS) :
    WP isa (countLoop .x14 corBody) s fun t =>
      wv t.mem B dO n + 2 ^ (64 * n) * ((t.gpr .x13).toNat + b.toNat * ((t.gpr .x2).toNat / 2 ^ 63)) =
        wv s.mem B dO n + b.toNat * (2 * wv s.mem B dS n) + (s.gpr .x13).toNat ∧
      t.gpr .x2 = word s.mem B (dS + 8 * (n - 1)) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep corRegs s t ∧ t.gpr .x16 = off B (dO + 8 * n) ∧
      t.gpr .x17 = off B (dS + 8 * n) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .x16 = off B (dO + 8 * i) ∧ t.gpr .x17 = off B (dS + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wv t.mem B dO i + 2 ^ (64 * i) * ((t.gpr .x13).toNat + b.toNat * ((t.gpr .x2).toNat / 2 ^ 63)) =
        wv s.mem B dO i + b.toNat * (2 * wv s.mem B dS i) + (s.gpr .x13).toNat ∧
      (0 < i → t.gpr .x2 = word s.mem B (dS + 8 * (i - 1))) ∧ Keep corRegs s t
  refine WP.mono (wp_countdown (body := .block (corBody ++ ([.subImm .x .x14 .x14 1] : List Instr)))
    (cnt := .x14) (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv
    (fun i hi t ⟨j16, j17, jout, jeq, jt2, jk⟩ hc => ?_)
    ⟨by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, by simp [wv, h2], fun h => absurd h (by decide),
      Keep.refl _ _⟩ h14)
    fun t ⟨j16, j17, jout, jeq, jt2, jk⟩ => ⟨jeq, jt2 (by omega_using [hn]), jout, jk, j16, j17⟩
  have hs' := hs.congr jk.wr
  have t15 : t.gpr .x15 = mask b := (jk.gpr .x15 (by decide)).trans h15
  have t7 : t.gpr .x7 = 0 := (jk.gpr .x7 (by decide)).trans h7
  have hst : WP isa (.block (corBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      (t'.gpr .x16 = off B (dO + 8 * i + 8) ∧ t'.gpr .x17 = off B (dS + 8 * i + 8) ∧
        t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 ∧ t'.gpr .x2 = word t.mem B (dS + 8 * i) ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (corW (t.gpr .x13) (dbl (word t.mem B (dS + 8 * i)) (t.gpr .x2) &&& mask b) (word t.mem B (dO + 8 * i))) ∧
        t'.gpr .x13 = corC (t.gpr .x13) (dbl (word t.mem B (dS + 8 * i)) (t.gpr .x2) &&& mask b)
          (word t.mem B (dO + 8 * i))) ∧
      Keep corRegs t t' := by
    refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
    unfold corBody twoS
    brun [t7, t15, j16, j17, off_add, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_using [hO, hi]),
      hs'.ld (show dS + 8 * i + 8 ≤ Z by omega_using [hS, hi]), hs'.st (show dO + 8 * i + 8 ≤ Z by omega_using [hO, hi])]
  refine WP.mono hst fun t' ⟨⟨l16, l17, l14, l2, lm, l13⟩, lk⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, fun _ => ?_, (jk.trans lk).mono (by decide)⟩, l14⟩
  · rw [l16, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_using []]
  · rw [l17, show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_using []]
  · rw [lm]; exact out_step _ jout (by omega_using [hO, hnw, hi])
  · have wo : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_using []) (by omega_using [hO, hnw, hi])
    have wx : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) := jout.word (by omega_using [hd, hi]) (by omega_using [hS, hnw, hi])
    have k := corw_arith (t.gpr .x13) (dbl (word t.mem B (dS + 8 * i)) (t.gpr .x2) &&& mask b)
      (word t.mem B (dO + 8 * i))
    have dv := dbl_toNat (word t.mem B (dS + 8 * i)) (t.gpr .x2)
    rw [and_mask_toNat', ← l13] at k
    rw [lm, wv_writeW_top _ _ _ _ _ (by omega_using [hO, hnw, hi]), wv_top s.mem B dO i, wv_top s.mem B dS i, l2, Nat.mul_succ,
      Nat.pow_add]
    rw [wo, wx] at k
    rw [wx] at dv
    rw [wo, wx]
    have hx := (word s.mem B (dS + 8 * i)).isLt
    generalize (word s.mem B (dS + 8 * i)).toNat = X at *
    generalize (t.gpr .x2).toNat / 2 ^ 63 = tb at *
    generalize (dbl (word s.mem B (dS + 8 * i)) (t.gpr .x2)).toNat = D at *
    generalize b.toNat = M at *
    generalize (word s.mem B (dO + 8 * i)).toNat = xo at *
    generalize (corW (t.gpr .x13) (dbl (word s.mem B (dS + 8 * i)) (t.gpr .x2) &&& mask b)
      (word s.mem B (dO + 8 * i))).toNat = x' at *
    generalize (t'.gpr .x13).toNat = c' at *
    generalize (t.gpr .x13).toNat = c at *
    generalize 2 ^ (64 * i) = P at *
    have e2 : 2 * X + tb = D + 2 ^ 64 * (X / 2 ^ 63) := by omega_using [dv]
    have e3 : M * (2 * X) + M * tb = M * D + 2 ^ 64 * (M * (X / 2 ^ 63)) := by
      rw [← Nat.mul_add, e2, Nat.mul_add, Nat.mul_left_comm]
    grind
  · rw [l2, show i + 1 - 1 = i by omega_using []]
    exact jout.word (by omega_using [hd, hi]) (by omega_using [hS, hnw, hi])

/-- The estimate a digit computes from `u = u₂:u₁`, `s₀`'s reciprocal `v` and `s₀`: all ones where `u₂ ≥ s₀`. -/
abbrev qhA (v u2 u1 d : BitVec 64) : BitVec 64 :=
  mgq v u2 u1 d ||| 0 - (0 + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ u2.toNat + (~~~d).toNat + true.toNat)).toNat)

/-- `q̂²`'s low word off `x`, and the carry word. -/
abbrev sqW (q x : BitVec 64) : BitVec 64 := x + ~~~(q * q) + BitVec.ofNat 64 true.toNat
abbrev sqC (q x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (q.toNat * q.toNat / 2 ^ 64) -
    (0 + ~~~0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ x.toNat + (~~~(q * q)).toNat + true.toNat)).toNat)

/-- The digit's second block: `q̂` into `x1`, `q̂²` off the window's word 0 (at `[wX4]`'s word
`W - 2 m - 2`), its carry word into `x13`, and the pointers of the multiply-subtract. -/
theorem dEst_ok {s : State} {B : Addr} {Z eR eS W m : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h7 : s.gpr .x7 = 0) (h6 : s.gpr .x6 = off B (8 * sV)) (h12 : s.gpr .x12 = BitVec.ofNat 64 W)
    (h10 : s.gpr .x10 = off B eR) (h11 : s.gpr .x11 = off B eS) (hm : word s.mem B (8 * sCnt) = BitVec.ofNat 64 m)
    (hW : 2 * m + 2 ≤ W) (hW' : W < 2 ^ 24) (hR : eR + 8 * W ≤ Z) (hH : 8 * 32 ≤ Z) (hR8 : 256 ≤ eR) :
    WP isa (.block (R2Div.quotMG ++ ([.subs .x .x4 .x2 .x5, .adc .x .x4 .x7 .x7, .sub .x .x4 .x7 .x4,
      .logic .orr .x .x1 .x14 .x4, ldh .x9 sCnt, .lsl .x .x3 .x9 4, .lsl .x .x4 .x12 3, .sub .x .x3 .x4 .x3,
      .subImm .x .x3 .x3 16, .add .x .x8 .x10 .x3, .mul .x .x3 .x1 .x1, .umulh .x4 .x1 .x1, ld .x5 .x8,
      .subs .x .x5 .x5 .x3, st .x5 .x8, .sbc .x .x6 .x7 .x7, .sub .x .x13 .x4 .x6] : List Instr) ++ rowPtrs)) s fun t =>
      (t.gpr .x1 = qhA (word s.mem B (8 * sV)) (s.gpr .x2) (s.gpr .x3) (s.gpr .x5) ∧
        t.mem = s.mem.writeW (off B (eR + (8 * W - 16 * m - 16)))
          (sqW (t.gpr .x1) (word s.mem B (eR + (8 * W - 16 * m - 16)))) ∧
        t.gpr .x13 = sqC (t.gpr .x1) (word s.mem B (eR + (8 * W - 16 * m - 16))) ∧
        t.gpr .x8 = off B (eR + (8 * W - 16 * m - 16)) ∧
        t.gpr .x16 = off B (eR + (8 * W - 16 * m - 16) + 8) ∧ t.gpr .x17 = off B (eS + 8 * (W / 2 - m)) ∧
        t.gpr .x2 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 (m + 1)) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x8, .x9, .x13, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  have e8 : off B eR + (BitVec.ofNat 64 W <<< 3 - BitVec.ofNat 64 m <<< 4 - BitVec.ofNat 64 16) =
      off B (eR + (8 * W - 16 * m - 16)) := by
    rw [shl_ofNat (show W * 2 ^ 3 < 2 ^ 64 by omega_using [hW']), shl_ofNat (show m * 2 ^ 4 < 2 ^ 64 by omega_using [hW, hW']),
      ofNat_sub_ofNat (by omega_using [hW]) (by omega_using [hW']), ofNat_sub_ofNat (by omega_using [hW]) (by omega_using [hW']), off_add]
    congr 2; omega_using []
  have e17 : off B eS + (BitVec.ofNat 64 W >>> 1 - BitVec.ofNat 64 m) <<< 3 = off B (eS + 8 * (W / 2 - m)) := by
    have : BitVec.ofNat 64 W >>> 1 = BitVec.ofNat 64 (W / 2) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega_using [hW']
    rw [this, ofNat_sub_ofNat (by omega_using [hW]) (by omega_using [hW']), shl_ofNat (show (W / 2 - m) * 2 ^ 3 < 2 ^ 64 by omega_using [hW']), off_add]
    congr 2; omega_using []
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x1, .x3, .x4, .x5, .x6, .x8, .x9, .x13, .x14, .x15, .x16, .x17] (Q := fun t =>
      t.gpr .x1 = qhA (word s.mem B (8 * sV)) (s.gpr .x2) (s.gpr .x3) (s.gpr .x5) ∧
        t.mem = s.mem.writeW (off B (eR + (8 * W - 16 * m - 16)))
          (sqW (t.gpr .x1) (word s.mem B (eR + (8 * W - 16 * m - 16)))) ∧
        t.gpr .x13 = sqC (t.gpr .x1) (word s.mem B (eR + (8 * W - 16 * m - 16))) ∧
        t.gpr .x8 = off B (eR + (8 * W - 16 * m - 16))) (by
    brun [exec_sbc_x', h0, h7, h6, h12, h10, hm, e8, r2d_exec_tst, r2d_exec_cselc, CondCode.holds, R2Div.quotMG,
      hdr_enc (show sCnt < 32 by decide), hs.ld (show 8 * sV + 8 ≤ Z by simp only [sV, sFn]; omega_using [hH]),
      hs.ld (show 8 * sCnt + 8 ≤ Z by rw [show 8 * sCnt = 208 from rfl]; omega_using [hH]),
      hs.ld (show eR + (8 * W - 16 * m - 16) + 8 ≤ Z by omega_using [hW, hR]),
      hs.st (show eR + (8 * W - 16 * m - 16) + 8 ≤ Z by omega_using [hW, hR])]
    all_goals rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨t1, tm, t13, t8⟩, tk⟩ => ?_
  have hst := hs.congr tk.wr
  have hmt : word t.mem B (8 * sCnt) = BitVec.ofNat 64 m := by
    rw [tm, (writeW_outside _ B _ (by omega_using [hW, hR, hn])).word (by rw [show 8 * sCnt = 208 from rfl]; omega_using [hR8])
      (by rw [show 8 * sCnt = 208 from rfl]; omega_using []), hm]
  refine WP.mono (WP.keep [.x2, .x3, .x6, .x14, .x16, .x17] (Q := fun t' =>
      t'.gpr .x16 = off B (eR + (8 * W - 16 * m - 16) + 8) ∧ t'.gpr .x17 = off B (eS + 8 * (W / 2 - m)) ∧
        t'.gpr .x2 = 0 ∧ t'.gpr .x14 = BitVec.ofNat 64 (m + 1) ∧ t'.mem = t.mem) (by
    unfold rowPtrs
    brun [t8, (tk.gpr .x0 (by decide)).trans h0, (tk.gpr .x12 (by decide)).trans h12,
      (tk.gpr .x11 (by decide)).trans h11, hmt, e17, off_add, BitVec.ofNat_add_ofNat,
      hdr_enc (show sCnt < 32 by decide), hst.ld (show 8 * sCnt + 8 ≤ Z by rw [show 8 * sCnt = 208 from rfl]; omega_using [hH])]) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨u16, u17, u2, u14, um⟩, uk⟩ => ?_
  refine ⟨⟨by rw [uk.gpr .x1 (by decide)]; exact t1, by rw [um, tm, uk.gpr .x1 (by decide)],
    by rw [uk.gpr .x13 (by decide), uk.gpr .x1 (by decide)]; exact t13, by rw [uk.gpr .x8 (by decide)]; exact t8,
    u16, u17, u2, u14⟩, (tk.trans uk).mono (by decide)⟩

/-- `rowPtrs`: the row pointers from the window's base `x8` and the count `m` in `sCnt`. -/
theorem rowPtrs_ok {s : State} {B : Addr} {Z d eS W m : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h8 : s.gpr .x8 = off B d) (h12 : s.gpr .x12 = BitVec.ofNat 64 W) (h11 : s.gpr .x11 = off B eS)
    (hm : word s.mem B (8 * sCnt) = BitVec.ofNat 64 m) (hW : 2 * m + 2 ≤ W) (hW' : W < 2 ^ 24) (hH : 8 * 32 ≤ Z) :
    WP isa (.block rowPtrs) s fun t =>
      (t.gpr .x16 = off B (d + 8) ∧ t.gpr .x17 = off B (eS + 8 * (W / 2 - m)) ∧ t.gpr .x2 = 0 ∧
        t.gpr .x14 = BitVec.ofNat 64 (m + 1) ∧ t.mem = s.mem) ∧ Keep [.x2, .x3, .x6, .x14, .x16, .x17] s t := by
  have e17 : off B eS + (BitVec.ofNat 64 W >>> 1 - BitVec.ofNat 64 m) <<< 3 = off B (eS + 8 * (W / 2 - m)) := by
    have : BitVec.ofNat 64 W >>> 1 = BitVec.ofNat 64 (W / 2) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega_using [hW']
    rw [this, ofNat_sub_ofNat (by omega_using [hW]) (by omega_using [hW']), shl_ofNat (show (W / 2 - m) * 2 ^ 3 < 2 ^ 64 by omega_using [hW']), off_add]
    congr 2; omega_using []
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  unfold rowPtrs
  brun [h0, h8, h12, h11, hm, e17, off_add, BitVec.ofNat_add_ofNat, hdr_enc (show sCnt < 32 by decide),
    hs.ld (show 8 * sCnt + 8 ≤ Z by rw [show 8 * sCnt = 208 from rfl]; omega_using [hH])]

/-- `correct`'s head: `b q̂ + b (q̂ - 1)` into the window's word 0 (`b` in `x9`), the carry into `x13`, and the row
pointers. -/
theorem cHead_ok {s : State} {B : Addr} {Z d eS W m : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = off B d) (h12 : s.gpr .x12 = BitVec.ofNat 64 W)
    (h11 : s.gpr .x11 = off B eS) (hm : word s.mem B (8 * sCnt) = BitVec.ofNat 64 m) (hW : 2 * m + 2 ≤ W)
    (hW' : W < 2 ^ 24) (hH : 8 * 32 ≤ Z) (hd : 256 ≤ d) (hdZ : d + 8 ≤ Z) :
    WP isa (.block (([.sub .x .x15 .x7 .x9, .logic .and .x .x4 .x1 .x15, .subImm .x .x5 .x1 1,
      .logic .and .x .x5 .x5 .x15, ld .x3 .x8, .adds .x .x3 .x3 .x4, .adc .x .x13 .x7 .x7, .adds .x .x3 .x3 .x5,
      .adc .x .x13 .x13 .x7, st .x3 .x8] : List Instr) ++ rowPtrs)) s fun t =>
      (t.mem = s.mem.writeW (off B d) (corW (s.gpr .x1 &&& (0 - s.gpr .x9))
          ((s.gpr .x1 - BitVec.ofNat 64 1) &&& (0 - s.gpr .x9)) (word s.mem B d)) ∧
        t.gpr .x13 = corC (s.gpr .x1 &&& (0 - s.gpr .x9)) ((s.gpr .x1 - BitVec.ofNat 64 1) &&& (0 - s.gpr .x9))
          (word s.mem B d) ∧
        t.gpr .x15 = 0 - s.gpr .x9 ∧ t.gpr .x16 = off B (d + 8) ∧ t.gpr .x17 = off B (eS + 8 * (W / 2 - m)) ∧
        t.gpr .x2 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 (m + 1)) ∧
      Keep [.x2, .x3, .x4, .x5, .x6, .x13, .x14, .x15, .x16, .x17] s t := by
  have hn := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x13, .x15] (Q := fun t =>
      t.mem = s.mem.writeW (off B d) (corW (s.gpr .x1 &&& (0 - s.gpr .x9))
          ((s.gpr .x1 - BitVec.ofNat 64 1) &&& (0 - s.gpr .x9)) (word s.mem B d)) ∧
        t.gpr .x13 = corC (s.gpr .x1 &&& (0 - s.gpr .x9)) ((s.gpr .x1 - BitVec.ofNat 64 1) &&& (0 - s.gpr .x9))
          (word s.mem B d) ∧ t.gpr .x15 = 0 - s.gpr .x9) (by
    brun [h7, h8, hs.ld hdZ, hs.st hdZ]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨tm, t13, t15⟩, tk⟩ => ?_
  have hmt : word t.mem B (8 * sCnt) = BitVec.ofNat 64 m := by
    rw [tm, (writeW_outside _ B _ (by omega_using [hdZ, hn])).word (by rw [show 8 * sCnt = 208 from rfl]; omega_using [hd])
      (by rw [show 8 * sCnt = 208 from rfl]; omega_using []), hm]
  refine WP.mono (rowPtrs_ok (hs.congr tk.wr) ((tk.gpr .x0 (by decide)).trans h0) ((tk.gpr .x8 (by decide)).trans h8)
    ((tk.gpr .x12 (by decide)).trans h12) ((tk.gpr .x11 (by decide)).trans h11) hmt hW hW' hH)
    fun u ⟨⟨u16, u17, u2, u14, um⟩, uk⟩ => ⟨⟨by rw [um, tm], by rw [uk.gpr .x13 (by decide), t13],
      by rw [uk.gpr .x15 (by decide), t15], u16, u17, u2, u14⟩, (tk.trans uk).mono (by decide)⟩

/-- `correct`'s tail: the carry added to the window's top word, `q̂ - b`, and the sign `b (1 - c)`. -/
theorem cTail_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h7 : s.gpr .x7 = 0)
    (h16 : s.gpr .x16 = off B d) (hdZ : d + 8 ≤ Z) :
    WP isa (.block [ld .x3 .x16, .adds .x .x3 .x3 .x13, st .x3 .x16, .adc .x .x4 .x7 .x7, .sub .x .x1 .x1 .x9,
      movi .x5 1, .logic .eor .x .x4 .x4 .x5, .logic .and .x .x9 .x9 .x4]) s fun t =>
      (t.mem = s.mem.writeW (off B d) (word s.mem B d + s.gpr .x13 + BitVec.ofNat 64 false.toNat) ∧
        t.gpr .x1 = s.gpr .x1 - s.gpr .x9 ∧
        t.gpr .x9 = s.gpr .x9 &&& ((0 + 0 + BitVec.ofNat 64
          (decide (2 ^ 64 ≤ (word s.mem B d).toNat + (s.gpr .x13).toNat + false.toNat)).toNat) ^^^
            BitVec.setWidth 64 1#16)) ∧
      Keep [.x1, .x3, .x4, .x5, .x9] s t :=
  WP.keep _ (by brun [h7, h16, hs.ld hdZ, hs.st hdZ]) (by decide) (by decide) (by decide +kernel)

theorem neg_bit_mask (b : Bool) : (0 : BitVec 64) - BitVec.ofNat 64 b.toNat = mask b := by cases b <;> rfl

theorem addc_arith (x y : BitVec 64) :
    (x + y + BitVec.ofNat 64 false.toNat).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ x.toNat + y.toNat + false.toNat)).toNat =
      x.toNat + y.toNat := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat_false, Nat.add_zero]
  by_cases c : 2 ^ 64 ≤ x.toNat + y.toNat <;>
    simp only [c, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_using [c]

theorem wv_split3 (m : Mem) (B : Addr) (d n : Nat) :
    wv m B d (n + 2) = (word m B d).toNat +
      2 ^ 64 * (wv m B (d + 8) n + 2 ^ (64 * n) * (word m B (d + 8 + 8 * n)).toNat) := by
  have e := wv_add m B d 1 (n + 1)
  rw [show 1 + (n + 1) = n + 2 by omega_using []] at e
  rw [e, wv_top m B (d + 8 * 1) n, show d + 8 * 1 = d + 8 by omega_using []]
  simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_one]

theorem sign_clear (bb c : Bool) :
    BitVec.ofNat 64 bb.toNat &&& ((0 + 0 + BitVec.ofNat 64 c.toNat) ^^^ BitVec.setWidth 64 1#16) =
      BitVec.ofNat 64 (bb && !c).toNat := by cases bb <;> cases c <;> rfl

abbrev corrRegs : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x9, .x13, .x14, .x15, .x16, .x17]

/-- `correct` on the window of `m + 3` words at `d` (`x8`), `S` the `m + 1` words at `e` (the root's word
`W / 2 - m`), its top word below `2^63`, the sign `b` in `x9` and `q̂` in `x1` (at least 1 where `b`): `b (2 S β +
2 q̂ - 1)` added, the carry out `c`, `q̂ - b` and the sign `b (1 - c)`. -/
theorem correct_ok {s : State} {B : Addr} {Z d eS W m : Nat} {bb : Bool} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = off B d) (h12 : s.gpr .x12 = BitVec.ofNat 64 W)
    (h11 : s.gpr .x11 = off B eS) (hm : word s.mem B (8 * sCnt) = BitVec.ofNat 64 m)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 bb.toNat) (hW : 2 * m + 2 ≤ W) (hW' : W < 2 ^ 24) (hH : 8 * 32 ≤ Z)
    (hd : 256 ≤ d) (hdZ : d + 8 * (m + 3) ≤ Z) (hSZ : eS + 8 * W ≤ Z) (hS8 : 256 ≤ eS)
    (hdS : d + 8 * (m + 3) ≤ eS ∨ eS + 8 * W ≤ d) :
    WP isa correct s fun t =>
      Outside B d (8 * (m + 3)) s.mem t.mem ∧ Keep corrRegs s t ∧
      ∃ c : Bool, t.gpr .x9 = BitVec.ofNat 64 (bb && !c).toNat ∧ t.gpr .x1 = s.gpr .x1 - BitVec.ofNat 64 bb.toNat ∧
        ((bb = true → 1 ≤ (s.gpr .x1).toNat) → (word s.mem B (eS + 8 * (W / 2 - m) + 8 * m)).toNat < 2 ^ 63 →
          wv t.mem B d (m + 3) + 2 ^ (64 * (m + 3)) * c.toNat = wv s.mem B d (m + 3) +
            bb.toNat * (2 * wv s.mem B (eS + 8 * (W / 2 - m)) (m + 1) * 2 ^ 64 + 2 * (s.gpr .x1).toNat - 1)) := by
  have hn := hs.nowrap
  unfold correct
  simp only [seqs]
  refine WP.seq (WP.mono (cHead_ok hs h0 h7 h8 h12 h11 hm hW hW' hH hd (by omega))
    fun t1 ⟨⟨m1, x13₁, x15₁, x16₁, x17₁, x2₁, x14₁⟩, k1⟩ => ?_)
  rw [h9, neg_bit_mask] at x15₁ m1 x13₁
  have hs1 := hs.congr k1.wr
  refine WP.seq (WP.mono (corLoop_ok (b := bb) (n := m + 1) hs1 x16₁ x17₁ x14₁ x2₁
    ((k1.gpr .x7 (by decide)).trans h7) x15₁ (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t2 ⟨eq2, t22, out2, k2, a16, a17⟩ => ?_)
  have hs2 := hs1.congr k2.wr
  refine WP.mono (cTail_ok hs2 ((k2.gpr .x7 (by decide)).trans ((k1.gpr .x7 (by decide)).trans h7)) a16 (by omega))
    fun t ⟨⟨m3, x1₃, x9₃⟩, k3⟩ => ?_
  have q2 : t2.gpr .x1 = s.gpr .x1 := (k2.gpr .x1 (by decide)).trans (k1.gpr .x1 (by decide))
  have b2 : t2.gpr .x9 = BitVec.ofNat 64 bb.toNat := by rw [k2.gpr .x9 (by decide), k1.gpr .x9 (by decide), h9]
  have o1 : Outside B d 8 s.mem t1.mem := by rw [m1]; exact writeW_outside _ _ _ (by omega)
  have o3 : Outside B (d + 8 + 8 * (m + 1)) 8 t2.mem t.mem := by rw [m3]; exact writeW_outside _ _ _ (by omega)
  refine ⟨((o1.mono (by omega) (by omega)).trans (out2.mono (by omega) (by omega))).trans
      (o3.mono (by omega) (by omega)), ((k1.trans k2).trans k3).mono (by decide),
    decide (2 ^ 64 ≤ (word t2.mem B (d + 8 + 8 * (m + 1))).toNat + (t2.gpr .x13).toNat + false.toNat),
    by rw [x9₃, b2, sign_clear], by rw [x1₃, q2, b2], fun hq htop => ?_⟩
  -- The words, through the writes.
  have S1 : wv t1.mem B (eS + 8 * (W / 2 - m)) (m + 1) = wv s.mem B (eS + 8 * (W / 2 - m)) (m + 1) :=
    o1.wv (by omega) (by omega)
  have W11 : wv t1.mem B (d + 8) (m + 1) = wv s.mem B (d + 8) (m + 1) := o1.wv (by omega) (by omega)
  have xt1 : word t1.mem B (d + 8 + 8 * (m + 1)) = word s.mem B (d + 8 + 8 * (m + 1)) := o1.word (by omega) (by omega)
  have xt2 : word t2.mem B (d + 8 + 8 * (m + 1)) = word s.mem B (d + 8 + 8 * (m + 1)) := by
    rw [out2.word (by omega) (by omega), xt1]
  have top0 : (t2.gpr .x2).toNat / 2 ^ 63 = 0 := by
    rw [t22, show m + 1 - 1 = m by omega, o1.word (by omega) (by omega)]; exact Nat.div_eq_of_lt htop
  have x0t : word t.mem B d = corW (s.gpr .x1 &&& mask bb) ((s.gpr .x1 - BitVec.ofNat 64 1) &&& mask bb)
      (word s.mem B d) := by
    rw [o3.word (by omega) (by omega), out2.word (by omega) (by omega), m1, word_writeW_self]
  have W1t : wv t.mem B (d + 8) (m + 1) = wv t2.mem B (d + 8) (m + 1) := o3.wv (by omega) (by omega)
  have xtt : word t.mem B (d + 8 + 8 * (m + 1)) = word t2.mem B (d + 8 + 8 * (m + 1)) + t2.gpr .x13 +
      BitVec.ofNat 64 false.toNat := by rw [m3, word_writeW_self]
  have A := corw_arith (s.gpr .x1 &&& mask bb) ((s.gpr .x1 - BitVec.ofNat 64 1) &&& mask bb) (word s.mem B d)
  rw [← x13₁, and_mask_toNat', and_mask_toNat'] at A
  have Cq := addc_arith (word t2.mem B (d + 8 + 8 * (m + 1))) (t2.gpr .x13)
  rw [top0, Nat.mul_zero, Nat.add_zero, S1, W11] at eq2
  have hqb : bb.toNat * (s.gpr .x1).toNat + bb.toNat * (s.gpr .x1 - BitVec.ofNat 64 1).toNat =
      bb.toNat * (2 * (s.gpr .x1).toNat - 1) := by
    cases bb
    · simp
    · have q1 := hq rfl
      have : (s.gpr .x1 - BitVec.ofNat 64 1).toNat = (s.gpr .x1).toNat - 1 := by
        rw [BitVec.toNat_sub]; have := (s.gpr .x1).isLt; simp; omega
      rw [Bool.toNat_true, this]; omega
  rw [Nat.add_assoc, hqb] at A
  rw [wv_split3, wv_split3, x0t, W1t, xtt]
  have e64 : 2 ^ (64 * (m + 3)) = 2 ^ 64 * 2 ^ (64 * (m + 1)) * 2 ^ 64 := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  rw [e64, ← xt2]
  have := combine3 (P := 2 ^ 64) (Q := 2 ^ (64 * (m + 1))) A eq2 Cq
  rw [this]
  have hE : bb.toNat * (2 * (s.gpr .x1).toNat - 1) +
      2 ^ 64 * (bb.toNat * (2 * wv s.mem B (eS + 8 * (W / 2 - m)) (m + 1))) =
      bb.toNat * (2 * wv s.mem B (eS + 8 * (W / 2 - m)) (m + 1) * 2 ^ 64 + 2 * (s.gpr .x1).toNat - 1) := by
    cases bb
    · simp
    · have := hq rfl
      rw [Bool.toNat_true, Nat.one_mul, Nat.one_mul, Nat.one_mul]
      have e : 2 ^ 64 * (2 * wv s.mem B (eS + 8 * (W / 2 - m)) (m + 1)) =
        2 * wv s.mem B (eS + 8 * (W / 2 - m)) (m + 1) * 2 ^ 64 := by ring
      omega
  rw [hE]

/-- A word and the next below, halved: `⌊(h 2^64 + l) / 2⌋ mod 2^64`. -/
abbrev half2 (h l : BitVec 64) : BitVec 64 := h <<< 63 ||| l >>> 1

theorem half2_toNat (h l : BitVec 64) : (half2 h l).toNat = (h.toNat % 2) * 2 ^ 63 + l.toNat / 2 := by
  have hl := l.isLt
  have h1 : (h <<< 63).toNat = (h.toNat % 2) * 2 ^ 63 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; have := h.isLt; omega_using []
  have h2 : (l >>> 1).toNat = l.toNat / 2 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd := sq_and_shl_small h (l >>> 1) 63 (by rw [h2]; omega_using [])
  unfold half2
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
  omega_using []

theorem u_val (x2 x1 x0 : BitVec 64) (h2 : x2.toNat ≤ 1) :
    v2 (half2 x2 x1) (half2 x1 x0) = (x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat) / 2 := by
  have := x1.isLt; have := x0.isLt
  simp only [v2, half2_toNat]
  omega_using [h2]

/-- The top three words of a window of `m + 3`, the top one at most 1, halved: `⌊V / (2 β^m)⌋`. -/
theorem win_u (mm : Mem) (B : Addr) (d m : Nat) (h2 : (word mm B (d + 8 * (m + 2))).toNat ≤ 1) :
    v2 (half2 (word mm B (d + 8 * (m + 2))) (word mm B (d + 8 * (m + 1))))
      (half2 (word mm B (d + 8 * (m + 1))) (word mm B (d + 8 * m))) =
      wv mm B d (m + 3) / (2 * 2 ^ (64 * m)) := by
  rw [u_val _ _ _ h2, wv_add mm B d m 3]
  have e3 : wv mm B (d + 8 * m) 3 = (word mm B (d + 8 * m)).toNat +
      2 ^ 64 * ((word mm B (d + 8 * (m + 1))).toNat + 2 ^ 64 * (word mm B (d + 8 * (m + 2))).toNat) := by
    simp only [wv]
    rw [show d + 8 * m + 8 * 1 = d + 8 * (m + 1) by omega_using [], show d + 8 * m + 8 * 2 = d + 8 * (m + 2) by omega_using [],
      show d + 8 * m + 8 * 0 = d + 8 * m by omega_using []]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.mul_one]
    ring
  rw [e3, Nat.mul_comm 2, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wv_lt _ _ _ _), Nat.zero_add]
  congr 1
  ring

theorem qhA_val {v u2 u1 d : BitVec 64} (hd : 2 ^ 63 ≤ d.toNat)
    (hv : v.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64) :
    (qhA v u2 u1 d).toNat = min (2 ^ 64 - 1) (v2 u2 u1 / d.toNat) := by
  have hdl := d.isLt; have hu1 := u1.isLt; have hu2 := u2.isLt
  unfold qhA
  rw [not_carry]
  by_cases c : u2.toNat < d.toNat
  · rw [decide_eq_false (by omega_using [c])]
    have m := mgq_val (v := v.toNat) (u := u2.toNat) (a := u1.toNat) hdl hd c hu1 hv
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at m
    rw [show (0 : BitVec 64) - (0 + 0 + BitVec.ofNat 64 false.toNat) = 0 from rfl,
      show ∀ x : BitVec 64, x ||| 0 = x from fun x => by simp, m]
    have : (u2.toNat * 2 ^ 64 + u1.toNat) / d.toNat < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by omega_using [hd])]
      have := Nat.mul_le_mul_right (2 ^ 64) (show u2.toNat + 1 ≤ d.toNat by omega_using [c])
      rw [Nat.add_mul, Nat.one_mul] at this
      rw [Nat.mul_comm]; omega_using [c]
    simp only [v2]; omega_using [m]
  · rw [decide_eq_true (by omega_using [c])]
    rw [show (0 : BitVec 64) - (0 + 0 + BitVec.ofNat 64 true.toNat) = BitVec.allOnes 64 from by decide,
      BitVec.or_allOnes, BitVec.toNat_allOnes]
    have : 2 ^ 64 ≤ v2 u2 u1 / d.toNat := by
      rw [Nat.le_div_iff_mul_le (by omega_using [hd])]
      have := Nat.mul_le_mul_left (2 ^ 64) (show d.toNat ≤ u2.toNat by omega_using [c])
      simp only [v2]; rw [Nat.mul_comm u2.toNat]; omega_using [c]
    omega_using [this]

theorem sqw_arith (q x : BitVec 64) :
    (sqW q x).toNat + q.toNat * q.toNat = x.toNat + 2 ^ 64 * (sqC q x).toNat := by
  have h := msw_arith q q 0 x
  have e1 : msW q q 0 x = sqW q x := by simp [msW, msLo, sqW]
  have e2 : msC q q 0 x = sqC q x := by
    simp [msC, msLo, sqC]
    rw [decide_eq_false (by omega_using [])]; rfl
  rw [e1, e2] at h
  simpa using h

/-- `dTop`'s word: `x - c`, and the borrow. -/
theorem subw_arith (x c : BitVec 64) :
    (x + ~~~c + BitVec.ofNat 64 true.toNat).toNat + c.toNat =
      x.toNat + 2 ^ 64 * (!decide (2 ^ 64 ≤ x.toNat + (~~~c).toNat + true.toNat)).toNat := by
  have hx := x.isLt; have hc := c.isLt
  have n1 : (~~~c).toNat = 2 ^ 64 - 1 - c.toNat := by rw [BitVec.toNat_not]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, n1, Bool.toNat_true]
  by_cases h : 2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - c.toNat) + 1 <;>
    simp only [h, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega_using [h]

theorem borrow_bit (C : Bool) :
    (0 : BitVec 64) - (0 + ~~~0 + BitVec.ofNat 64 C.toNat) = BitVec.ofNat 64 (!C).toNat := by cases C <;> rfl

/-- `dTop`: the carry word off the window's top word, and the borrow into `x9`. -/
theorem dTop_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h7 : s.gpr .x7 = 0)
    (h16 : s.gpr .x16 = off B d) (hdZ : d + 8 ≤ Z) :
    WP isa (.block [ld .x3 .x16, .subs .x .x3 .x3 .x13, st .x3 .x16, .sbc .x .x5 .x7 .x7, .sub .x .x9 .x7 .x5]) s
      fun t => (t.mem = s.mem.writeW (off B d) (word s.mem B d + ~~~(s.gpr .x13) + BitVec.ofNat 64 true.toNat) ∧
        t.gpr .x9 = BitVec.ofNat 64
          (!decide (2 ^ 64 ≤ (word s.mem B d).toNat + (~~~(s.gpr .x13)).toNat + true.toNat)).toNat) ∧
      Keep [.x3, .x5, .x9] s t :=
  WP.keep _ (by brun [exec_sbc_x', h7, h16, hs.ld hdZ, hs.st hdZ, borrow_bit]) (by decide) (by decide)
    (by decide +kernel)

/-- `digit`'s first block: the remainder's top three words (`[wX4]`'s words `W - m - 2` to `W - m`) halved into
`x2:x3`, `s₀` into `x5`, the reciprocal's address into `x6`. -/
theorem dLoad_ok {s : State} {B : Addr} {Z eR W m p : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h10 : s.gpr .x10 = off B eR) (h12 : s.gpr .x12 = BitVec.ofNat 64 W) (hp : eR + 8 * (W - m) - 16 = p)
    (hm : word s.mem B (8 * sCnt) = BitVec.ofNat 64 m) (hm1 : 1 ≤ m) (hW : m + 2 ≤ W) (hW' : W < 2 ^ 24) (hH : 8 * 32 ≤ Z)
    (hR : eR + 8 * W ≤ Z) (hR8 : 256 ≤ eR) :
    WP isa (.block [ldh .x8 sCnt, .sub .x .x3 .x12 .x8, .lsl .x .x3 .x3 3, .add .x .x16 .x10 .x3,
      .subImm .x .x16 .x16 16, ld .x2 .x16 16, ld .x3 .x16 8, ld .x4 .x16, .lsl .x .x5 .x2 63, .lsr .x .x6 .x3 1,
      .logic .orr .x .x2 .x5 .x6, .lsl .x .x6 .x3 63, .lsr .x .x4 .x4 1, .logic .orr .x .x3 .x6 .x4, ldh .x5 sS0,
      .addImm .x .x6 .x0 (8 * sV)]) s fun t =>
      (t.gpr .x2 = half2 (word s.mem B (p + 16)) (word s.mem B (p + 8)) ∧
        t.gpr .x3 = half2 (word s.mem B (p + 8)) (word s.mem B p) ∧
        t.gpr .x5 = word s.mem B (8 * sS0) ∧ t.gpr .x6 = off B (8 * sV) ∧ t.mem = s.mem) ∧
      Keep [.x2, .x3, .x4, .x5, .x6, .x8, .x16] s t := by
  subst hp
  have hn := hs.nowrap
  have e16 : off B eR + (BitVec.ofNat 64 W - BitVec.ofNat 64 m) <<< 3 - BitVec.ofNat 64 16 =
      off B (eR + 8 * (W - m) - 16) := by
    rw [ofNat_sub_ofNat (by omega) (by omega), shl_ofNat (show (W - m) * 2 ^ 3 < 2 ^ 64 by omega), off_add,
      off_sub B (by omega)]
    congr 2; omega
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h0, h10, h12, hm, e16, off_add, hdr_enc (show sCnt < 32 by decide), hdr_enc (show sS0 < 32 by decide),
    hs.ld (show 8 * sCnt + 8 ≤ Z by rw [show 8 * sCnt = 208 from rfl]; omega),
    hs.ld (show 8 * sS0 + 8 ≤ Z by rw [show 8 * sS0 = 240 from rfl]; omega),
    hs.ld (show eR + 8 * (W - m) - 16 + 16 + 8 ≤ Z by omega), hs.ld (show eR + 8 * (W - m) - 16 + 8 + 8 ≤ Z by omega),
    hs.ld (show eR + 8 * (W - m) - 16 + 8 ≤ Z by omega)]

/-- `digit`'s last block: the digit `x1` into the root's word `W / 2 - m - 1`, `m + 1` into `sCnt`, and the digits
left, `W / 2 - (m + 1)`, into `x3`. -/
theorem dNext_ok {s : State} {B : Addr} {Z eS W m : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = off B eS) (h12 : s.gpr .x12 = BitVec.ofNat 64 W)
    (hm : word s.mem B (8 * sCnt) = BitVec.ofNat 64 m) (hW : 2 * m + 2 ≤ W) (hW' : W < 2 ^ 24) (hH : 8 * 32 ≤ Z)
    (hS : eS + 8 * W ≤ Z) :
    WP isa (.block [ldh .x9 sCnt, .lsr .x .x3 .x12 1, .sub .x .x3 .x3 .x9, .subImm .x .x3 .x3 1, .lsl .x .x3 .x3 3,
      .add .x .x3 .x11 .x3, st .x1 .x3, .addImm .x .x9 .x9 1, sth .x9 sCnt, .lsr .x .x3 .x12 1, .sub .x .x3 .x3 .x9]) s
      fun t => (t.mem = (s.mem.writeW (off B (eS + 8 * (W / 2 - m - 1))) (s.gpr .x1)).writeW (off B (8 * sCnt))
          (BitVec.ofNat 64 (m + 1)) ∧ t.gpr .x3 = BitVec.ofNat 64 (W / 2 - (m + 1))) ∧
      Keep [.x3, .x9] s t := by
  have hn := hs.nowrap
  have eW : BitVec.ofNat 64 W >>> 1 = BitVec.ofNat 64 (W / 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega_using [hW']
  have eA : off B eS + (BitVec.ofNat 64 (W / 2) - BitVec.ofNat 64 m - BitVec.ofNat 64 1) <<< 3 =
      off B (eS + 8 * (W / 2 - m - 1)) := by
    rw [ofNat_sub_ofNat (by omega_using [hW]) (by omega_using [hW']), ofNat_sub_ofNat (by omega_using [hW]) (by omega_using [hW']),
      shl_ofNat (show (W / 2 - m - 1) * 2 ^ 3 < 2 ^ 64 by omega_using [hW']), off_add]
    congr 2; omega_using []
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h0, h11, h12, hm, eW, eA, BitVec.ofNat_add_ofNat, ofNat_sub_ofNat (show m + 1 ≤ W / 2 by omega_using [hW]) (by omega_using [hW']),
    hdr_enc (show sCnt < 32 by decide), hs.ld (show 8 * sCnt + 8 ≤ Z by rw [show 8 * sCnt = 208 from rfl]; omega_using [hH]),
    hs.st (show 8 * sCnt + 8 ≤ Z by rw [show 8 * sCnt = 208 from rfl]; omega_using [hH]),
    hs.st (show eS + 8 * (W / 2 - m - 1) + 8 ≤ Z by omega_using [hW, hS])]

theorem band_toNat (b c : Bool) : (b && !c).toNat = b.toNat * (1 - c.toNat) := by cases b <;> cases c <;> rfl

theorem sub_bit_toNat (x : BitVec 64) (b : Bool) (h : b = true → 1 ≤ x.toNat) :
    (x - BitVec.ofNat 64 b.toNat).toNat = x.toNat - b.toNat := by
  cases b
  · simp
  · have := h rfl
    have := x.isLt
    rw [BitVec.toNat_sub]; simp; omega_arith

/-- The three corrections of a digit's estimate `q̂`, at most three above the digit `q`: the remainder and
the digit. -/
theorem digit_fix {E Sv Rb V0 V1 V2 V3 qh x4 x5 x6 q : Nat} {b0 c1 c2 c3 : Bool}
    (E0 : Enc E (2 * Sv * 2 ^ 64) Rb V0 qh b0.toNat) (hV0 : V0 < E) (hV1 : V1 < E) (hV2 : V2 < E) (hV3 : V3 < E) (hQ : qOf (2 * Sv * 2 ^ 64) qh < E)
    (qlo : q ≤ qh) (qhi : qh ≤ q + 3) (hq : IsDigit (2 ^ 64) Sv Rb q)
    (v4 : (b0 = true → 1 ≤ qh) → V1 + E * c1.toNat = V0 + b0.toNat * (2 * Sv * 2 ^ 64 + 2 * qh - 1))
    (q4 : (b0 = true → 1 ≤ qh) → x4 = qh - b0.toNat)
    (v5 : ((b0 && !c1) = true → 1 ≤ x4) →
      V2 + E * c2.toNat = V1 + (b0 && !c1).toNat * (2 * Sv * 2 ^ 64 + 2 * x4 - 1))
    (q5 : ((b0 && !c1) = true → 1 ≤ x4) → x5 = x4 - (b0 && !c1).toNat)
    (v6 : ((b0 && !c1 && !c2) = true → 1 ≤ x5) →
      V3 + E * c3.toNat = V2 + (b0 && !c1 && !c2).toNat * (2 * Sv * 2 ^ 64 + 2 * x5 - 1))
    (q6 : ((b0 && !c1 && !c2) = true → 1 ≤ x5) → x6 = x5 - (b0 && !c1 && !c2).toNat)
    :
    V3 = Rb - qOf (2 * Sv * 2 ^ 64) q ∧ x6 = q := by
  have pos : ∀ {V qh' : Nat} {b : Bool}, Enc E (2 * Sv * 2 ^ 64) Rb V qh' b.toNat → V < E → b = true → 1 ≤ qh' :=
    fun {V qh' b} h hV hb => by
      have sg := h.sign hV
      rw [hb] at sg
      rcases Nat.eq_zero_or_pos qh' with h0 | h0
      · rw [h0] at sg; simp only [qOf, Nat.zero_mul] at sg; split at sg <;> simp at sg <;> omega
      · exact h0
  have p0 := pos E0 hV0
  have a1 := v4 p0
  have e4 := q4 p0
  have E1 := E0.correct hV0 hQ (Bool.toNat_le _) a1
  rw [← band_toNat, ← e4] at E1
  have p1 := pos E1 hV1
  have a2 := v5 p1
  have e5 := q5 p1
  have hQ1 : qOf (2 * Sv * 2 ^ 64) x4 < E := Nat.lt_of_le_of_lt (qOf_mono (by rw [e4]; exact Nat.sub_le _ _)) hQ
  have E2 := E1.correct hV1 hQ1 (Bool.toNat_le _) a2
  rw [← band_toNat, ← e5] at E2
  have p2 := pos E2 hV2
  have a3 := v6 p2
  have e6 := q6 p2
  rw [e4] at a2
  rw [e5, e4] at a3
  rw [e6, e5, e4]
  simp only [band_toNat] at a2 a3 ⊢
  have dig1 : qOf (2 * Sv * 2 ^ 64) q ≤ Rb := by
    unfold qOf; rw [Nat.mul_comm]; exact hq.1
  have dig2 : Rb < qOf (2 * Sv * 2 ^ 64) (q + 1) := by
    unfold qOf; rw [Nat.mul_comm (q + 1)]; exact hq.2
  obtain ⟨hx, _, hV3⟩ := Enc.three dig1 dig2 qlo qhi E0 hV0 hV1 hV2 hV3 hQ
    (Bool.toNat_le c1) (Bool.toNat_le c2) (Bool.toNat_le c3) a1 a2 a3
  exact ⟨hV3, hx⟩

/-- A digit's multiply-subtract over the window's low word, middle and top word: `Enc` with the borrow. -/
theorem enc_of {x0 x0' W1 W1' xt xt' c0 c1 qh Sv m : Nat} {b : Bool} (A : x0' + qh * qh = x0 + 2 ^ 64 * c0)
    (Bq : W1' + qh * (2 * Sv) + c0 = W1 + 2 ^ (64 * (m + 1)) * c1) (C : xt' + c1 = xt + 2 ^ 64 * b.toNat) :
    Enc (2 ^ (64 * (m + 1 + 2))) (2 * Sv * 2 ^ 64) (x0 + 2 ^ 64 * (W1 + 2 ^ (64 * (m + 1)) * xt))
      (x0' + 2 ^ 64 * (W1' + 2 ^ (64 * (m + 1)) * xt')) qh b.toNat := by
  refine ⟨?_, Bool.toNat_le _⟩
  have e64 : 2 ^ (64 * (m + 1 + 2)) = 2 ^ 64 * 2 ^ (64 * (m + 1)) * 2 ^ 64 := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using []
  have key : qOf (2 * Sv * 2 ^ 64) qh = qh * qh + 2 ^ 64 * (qh * (2 * Sv)) := by unfold qOf; ring
  rw [key, e64, msub3 (P := 2 ^ 64) (Q := 2 ^ (64 * (m + 1))) A Bq C]
  ring

/-- A digit's estimate from the window's top three words halved and `s₀`'s reciprocal: at least the digit, at
most three above it, and a word; the window `R β² + P`, `S < β^m` and `S`'s top word zero. -/
theorem digit_est {mm : Mem} {B : Addr} {d e m Sv R P q : Nat} {v d0 x : BitVec 64}
    (hx : x = qhA v (half2 (word mm B (d + 8 * m + 16)) (word mm B (d + 8 * m + 8)))
      (half2 (word mm B (d + 8 * m + 8)) (word mm B (d + 8 * m))) d0)
    (hSv : wv mm B e (m + 1) = Sv) (hRv : wv mm B (d + 16) (m + 1) = R) (hPv : wv mm B d 2 = P) (hm1 : 1 ≤ m)
    (hd0 : Sv / 2 ^ (64 * (m - 1)) = d0.toNat) (hd1 : 2 ^ 63 ≤ d0.toNat) (hR2 : R ≤ 2 * Sv)
    (hq : IsDigit (2 ^ 64) Sv (R * (2 ^ 64 * 2 ^ 64) + P) q) (hv : v.toNat = (2 ^ 128 - 1) / d0.toNat - 2 ^ 64) :
    q ≤ x.toNat ∧ x.toNat ≤ q + 3 ∧ x.toNat ≤ 2 ^ 64 - 1 ∧ wv mm B d (m + 3) = R * (2 ^ 64 * 2 ^ 64) + P ∧
      Sv < 2 ^ (64 * m) ∧ word mm B (e + 8 * m) = 0 := by
  have V0 : wv mm B d (m + 3) = R * (2 ^ 64 * 2 ^ 64) + P := by
    have := wv_add mm B d 2 (m + 1)
    rw [show 2 + (m + 1) = m + 3 by omega_using [], show d + 8 * 2 = d + 16 by omega_using [], hRv, hPv] at this
    rw [this, show 2 ^ (64 * 2) = 2 ^ 64 * 2 ^ 64 by rfl]; ring
  have hPl : P < 2 ^ 64 * 2 ^ 64 := by rw [← hPv]; exact wv_lt _ _ _ _
  have hSl : Sv < 2 ^ (64 * m) := by
    have e' : 2 ^ (64 * m) = 2 ^ 64 * 2 ^ (64 * (m - 1)) := by rw [← Nat.pow_add]; congr 1; omega_using [hm1]
    rw [e', ← Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), hd0]; exact d0.isLt
  have rTop : (word mm B (d + 16 + 8 * m)).toNat ≤ 1 := top_le_one (by rw [hRv]; omega_using [hR2, hSl])
  have hwin := win_u mm B d m (by rw [show d + 8 * (m + 2) = d + 16 + 8 * m by omega_using []]; exact rTop)
  rw [show d + 8 * (m + 2) = d + 8 * m + 16 by omega_using [], show d + 8 * (m + 1) = d + 8 * m + 8 by omega_using [], V0] at hwin
  have qv : x.toNat = min (2 ^ 64 - 1) ((R * (2 ^ 64 * 2 ^ 64) + P) / (2 * 2 ^ (64 * m)) / d0.toNat) := by
    rw [hx, qhA_val hd1 hv, hwin]
  obtain ⟨qlo, qhi⟩ := est_bounds hm1 hd0 hd1 hR2 hPl hq
  rw [← qv] at qlo qhi
  exact ⟨qlo, qhi, by rw [qv]; exact Nat.min_le_left _ _, V0, hSl, top_zero (by rw [hSv]; exact hSl)⟩

abbrev digRegs : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x8, .x9, .x13, .x14, .x15, .x16, .x17]

/-- A digit, `m` of them so far (`1 ≤ m`): the window of `m + 3` words at `d` (word `W - 2 m - 2` of the
remainder at `eR`) less `q (2 S β + q)`, `S` the root's `m + 1` words from word `W / 2 - m` (at `eS`), and the
digit `q` into the root's word `W / 2 - m - 1`, `m + 1` into `sCnt`. -/
theorem digit_ok {s : State} {B : Addr} {Z eR eS W m : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h7 : s.gpr .x7 = 0) (h10 : s.gpr .x10 = off B eR) (h11 : s.gpr .x11 = off B eS)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 W) (hm : word s.mem B (8 * sCnt) = BitVec.ofNat 64 m) (hm1 : 1 ≤ m)
    (hW : 2 * m + 2 ≤ W) (hW' : W < 2 ^ 24) (hH : 8 * 32 ≤ Z) (hR : eR + 8 * W ≤ Z) (hR8 : 256 ≤ eR)
    (hS : eS + 8 * W ≤ Z) (hS8 : 256 ≤ eS) (hRS : eR + 8 * W ≤ eS ∨ eS + 8 * W ≤ eR) :
    WP isa digit s fun t => Keep digRegs s t ∧ t.gpr .x3 = BitVec.ofNat 64 (W / 2 - (m + 1)) ∧
      ∃ (mid : Mem) (y : BitVec 64), Outside B (eR + (8 * W - 16 * m - 16)) (8 * (m + 3)) s.mem mid ∧
        t.mem = (mid.writeW (off B (eS + 8 * (W / 2 - m - 1))) y).writeW (off B (8 * sCnt))
          (BitVec.ofNat 64 (m + 1)) ∧
        ∀ Sv R P q, wv s.mem B (eS + 8 * (W / 2 - m)) (m + 1) = Sv →
          wv s.mem B (eR + (8 * W - 16 * m - 16) + 16) (m + 1) = R →
          wv s.mem B (eR + (8 * W - 16 * m - 16)) 2 = P →
          Sv / 2 ^ (64 * (m - 1)) = (word s.mem B (8 * sS0)).toNat → 2 ^ 63 ≤ (word s.mem B (8 * sS0)).toNat →
          R ≤ 2 * Sv → IsDigit (2 ^ 64) Sv (R * (2 ^ 64 * 2 ^ 64) + P) q →
          (word s.mem B (8 * sV)).toNat = (2 ^ 128 - 1) / (word s.mem B (8 * sS0)).toNat - 2 ^ 64 →
          wv mid B (eR + (8 * W - 16 * m - 16)) (m + 3) = R * (2 ^ 64 * 2 ^ 64) + P - qOf (2 * Sv * 2 ^ 64) q ∧
            y.toNat = q := by
  have hn := hs.nowrap
  have eC : 8 * sCnt = 208 := rfl
  obtain ⟨d, hd⟩ : ∃ d, eR + (8 * W - 16 * m - 16) = d := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, eS + 8 * (W / 2 - m) = e := ⟨_, rfl⟩
  rw [hd, he]
  have hdS : d + 8 * (m + 3) ≤ eS ∨ eS + 8 * W ≤ d := by omega_using [hm1, hW, hRS, hd]
  have hed : e + 8 * (m + 1) ≤ d ∨ d + 8 * (m + 3) ≤ e := by omega_using [hW, he, hdS]
  have hd8 : 256 ≤ d := by omega_using [hR8, hd]
  have hdZ : d + 8 * (m + 3) ≤ Z := by omega_using [hm1, hW, hR, hd]
  unfold digit
  simp only [seqs]
  refine WP.seq (WP.mono (dLoad_ok (p := d + 8 * m) hs h0 h10 h12 (by omega_using [hm1, hW, hW', hR, hR8, hS, hRS, hd, he, hdS, hed, hd8, hdZ]) hm hm1 (by omega_using [hW]) hW' hH hR hR8)
    fun u ⟨⟨u2, u3, u5, u6, um⟩, uk⟩ => ?_)
  have hsu := hs.congr uk.wr
  refine WP.seq (WP.mono (dEst_ok (eR := eR) (eS := eS) (W := W) (m := m) hsu (by rw [uk.get .x0, h0]) (by rw [uk.get .x7, h7]) u6
    (by rw [uk.get .x12, h12]) (by rw [uk.get .x10, h10]) (by rw [uk.get .x11, h11]) (by rw [um]; exact hm)
    hW hW' hR hH hR8) fun t1 ⟨⟨q1, m1, c1, a81, a161, a171, a21, a141⟩, k1⟩ => ?_)
  rw [hd] at m1 c1 a81 a161
  rw [he] at a171
  have hs1 := hsu.congr k1.wr
  have x71 : t1.gpr .x7 = 0 := by rw [k1.get .x7, uk.get .x7, h7]
  refine WP.seq (WP.mono (msLoop_ok (n := m + 1) hs1 a161 a171 a141 a21 x71 (by omega_using []) (by omega_using [hm1, hW, hW', hH, hR, hR8, hS, hS8, hRS, hn, hd, he, hdS, hed, hd8, hdZ]) (by omega_using [hW, hR, hd])
    (by omega_using [hW, hS, he]) (by omega_using [hW, he, hdS])) fun t2 ⟨eq2, t22, out2, k2, a162, a172⟩ => ?_)
  have hs2 := hs1.congr k2.wr
  refine WP.seq (WP.mono (dTop_ok (d := d + 8 + 8 * (m + 1)) hs2 (by rw [k2.get .x7, x71]) a162 (by omega_using [hm1, hW, hR, hd]))
    fun t3 ⟨⟨m3, x93⟩, k3⟩ => ?_)
  have hs3 := hs2.congr k3.wr
  -- The window's frame so far.
  have o1 : Outside B d 8 s.mem t1.mem := by rw [m1, um]; exact writeW_outside _ _ _ (by omega_using [hm1, hW, hW', hH, hR, hR8, hS, hS8, hRS, hn, hd, he, hdS, hed, hd8, hdZ])
  have o3 : Outside B (d + 8 + 8 * (m + 1)) 8 t2.mem t3.mem := by rw [m3]; exact writeW_outside _ _ _ (by omega_using [hm1, hW, hW', hH, hR, hR8, hS, hS8, hRS, hn, hd, he, hdS, hed, hd8, hdZ])
  have oA : Outside B d (8 * (m + 3)) s.mem t3.mem :=
    ((o1.mono (by omega_using []) (by omega_using [])).trans (out2.mono (by omega_using []) (by omega_using []))).trans (o3.mono (by omega_using []) (by omega_using []))
  have hmO : ∀ {mm : Mem}, Outside B d (8 * (m + 3)) s.mem mm → word mm B (8 * sCnt) = BitVec.ofNat 64 m :=
    fun o => by rw [o.word (by rw [eC]; omega_using [hd8]) (by rw [eC]; omega_using []), hm]
  -- Registers through the multiply-subtract.
  have K3 : Keep digRegs s t3 := (((uk.trans k1).trans k2).trans k3).mono
  have r3 : ∀ r, r ∉ digRegs → t3.gpr r = s.gpr r := K3.gpr
  have x03 : t3.gpr .x0 = B := by rw [r3 .x0 (by decide), h0]
  have x73 : t3.gpr .x7 = 0 := by rw [r3 .x7 (by decide), h7]
  have x113 : t3.gpr .x11 = off B eS := by rw [r3 .x11 (by decide), h11]
  have x123 : t3.gpr .x12 = BitVec.ofNat 64 W := by rw [r3 .x12 (by decide), h12]
  have x83 : t3.gpr .x8 = off B d := by rw [k3.get .x8, k2.get .x8, a81]
  have x13' : t3.gpr .x1 = t1.gpr .x1 := by rw [k3.get .x1, k2.get .x1]
  -- The three corrections.
  refine WP.seq (WP.mono (correct_ok (d := d) (eS := eS) (W := W) (m := m) hs3 x03 x73 x83 x123 x113 (hmO oA) x93 hW hW' hH hd8 hdZ hS hS8
    hdS) fun t4 ⟨o4, k4, cc1, b4, x14, v4⟩ => ?_)
  have hs4 := hs3.congr k4.wr
  refine WP.seq (WP.mono (correct_ok (d := d) (eS := eS) (W := W) (m := m) hs4 (by rw [k4.get .x0, x03]) (by rw [k4.get .x7, x73])
    (by rw [k4.get .x8, x83]) (by rw [k4.get .x12, x123]) (by rw [k4.get .x11, x113]) (hmO (oA.trans o4)) b4 hW hW'
    hH hd8 hdZ hS hS8 hdS) fun t5 ⟨o5, k5, cc2, b5, x15, v5⟩ => ?_)
  have hs5 := hs4.congr k5.wr
  refine WP.seq (WP.mono (correct_ok (d := d) (eS := eS) (W := W) (m := m) hs5 (by rw [k5.get .x0, k4.get .x0, x03]) (by rw [k5.get .x7, k4.get .x7, x73])
    (by rw [k5.get .x8, k4.get .x8, x83]) (by rw [k5.get .x12, k4.get .x12, x123])
    (by rw [k5.get .x11, k4.get .x11, x113]) (hmO ((oA.trans o4).trans o5)) b5 hW hW' hH hd8 hdZ hS hS8
    hdS) fun t6 ⟨o6, k6, cc3, b6, x16, v6⟩ => ?_)
  have hs6 := hs5.congr k6.wr
  have oA6 : Outside B d (8 * (m + 3)) s.mem t6.mem := ((oA.trans o4).trans o5).trans o6
  refine WP.mono (dNext_ok hs6 (by rw [k6.get .x0, k5.get .x0, k4.get .x0, x03])
    (by rw [k6.get .x11, k5.get .x11, k4.get .x11, x113]) (by rw [k6.get .x12, k5.get .x12, k4.get .x12, x123])
    (hmO oA6) hW hW' hH hS) fun t ⟨⟨m7, x37⟩, k7⟩ => ?_
  refine ⟨(((((((uk.trans k1).trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).mono, x37, t6.mem,
    t6.gpr .x1, oA6, m7, ?_⟩
  intro Sv R P q hSv hRv hPv hd0 hd1 hR2 hq hv
  rw [he] at v4 v5 v6
  obtain ⟨qlo, qhi, qmax, V0, hSl, sTop⟩ := digit_est (x := t3.gpr .x1) (by rw [x13', q1, um, u2, u3, u5]) hSv hRv hPv
    hm1 hd0 hd1 hR2 hq hv
  generalize hqh : t3.gpr .x1 = qh at qlo qhi qmax x14 v4
  -- The multiply-subtract, `Enc` with the sign `b₀`.
  have Se1 : wv t1.mem B e (m + 1) = Sv := by rw [o1.wv (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]), hSv]
  have W11 : wv t1.mem B (d + 8) (m + 1) = wv s.mem B (d + 8) (m + 1) := o1.wv (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1])
  have tb0 : (t2.gpr .x2).toNat / 2 ^ 63 = 0 := by
    rw [t22, show m + 1 - 1 = m by omega_using [], o1.word (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]), sTop]; rfl
  rw [tb0, Nat.mul_zero, Nat.add_zero, Se1, W11, ← x13', hqh] at eq2
  have xt2 : word t2.mem B (d + 8 + 8 * (m + 1)) = word s.mem B (d + 8 + 8 * (m + 1)) := by
    rw [out2.word (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]), o1.word (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1])]
  have A := sqw_arith (t1.gpr .x1) (word u.mem B d)
  rw [← c1, ← x13', hqh, um] at A
  have C := subw_arith (word t2.mem B (d + 8 + 8 * (m + 1))) (t2.gpr .x13)
  have x03' : word t3.mem B d = sqW (t1.gpr .x1) (word s.mem B d) := by
    rw [o3.word (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]), out2.word (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]), m1, um, word_writeW_self]
  rw [← x13', hqh] at x03'
  have W13 : wv t3.mem B (d + 8) (m + 1) = wv t2.mem B (d + 8) (m + 1) := o3.wv (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1])
  have xt3 : word t3.mem B (d + 8 + 8 * (m + 1)) =
      word t2.mem B (d + 8 + 8 * (m + 1)) + ~~~(t2.gpr .x13) + BitVec.ofNat 64 true.toNat := by
    rw [m3, word_writeW_self]
  generalize hb0 : (!decide (2 ^ 64 ≤ (word t2.mem B (d + 8 + 8 * (m + 1))).toNat + (~~~(t2.gpr .x13)).toNat +
    true.toNat)) = b0 at C x93 v4 v5 v6 x14 x15 x16 b4 b5
  have E0 : Enc (2 ^ (64 * (m + 3))) (2 * Sv * 2 ^ 64) (R * (2 ^ 64 * 2 ^ 64) + P) (wv t3.mem B d (m + 3))
      qh.toNat b0.toNat := by
    rw [← V0, show m + 3 = m + 1 + 2 from rfl, wv_split3, wv_split3, x03', W13, xt3, ← xt2]
    exact enc_of A eq2 C
  have hQ0 : qOf (2 * Sv * 2 ^ 64) qh.toNat < 2 ^ (64 * (m + 3)) :=
    qOf_lt hSl qmax
  -- `S` and its top word, through the writes in the window.
  have oS : ∀ {mm : Mem}, Outside B d (8 * (m + 3)) s.mem mm →
      wv mm B e (m + 1) = Sv ∧ (word mm B (e + 8 * m)).toNat < 2 ^ 63 := fun {mm} o => by
    refine ⟨by rw [o.wv (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]), hSv], ?_⟩
    rw [o.word (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]) (by omega_using [hd, he, hdZ, hS, hn, hed, hW, hR, hm1]), sTop]; decide
  obtain ⟨S3, T3⟩ := oS oA
  obtain ⟨S4, T4⟩ := oS (oA.trans o4)
  obtain ⟨S5, T5⟩ := oS ((oA.trans o4).trans o5)
  exact digit_fix (x4 := (t4.gpr .x1).toNat) (x5 := (t5.gpr .x1).toNat) (x6 := (t6.gpr .x1).toNat)
    (c1 := cc1) (c2 := cc2) (c3 := cc3) E0 (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) hQ0 qlo qhi hq
    (fun h => by have := v4 h T3; rwa [S3] at this) (fun h => by rw [x14]; exact sub_bit_toNat _ _ h)
    (fun h => by have := v5 h T4; rwa [S4] at this) (fun h => by rw [x15]; exact sub_bit_toNat _ _ h)
    (fun h => by have := v6 h T5; rwa [S5] at this) (fun h => by rw [x16]; exact sub_bit_toNat _ _ h)

/-- `digits`' head: the bases, and `1` into `sCnt` and `x3`. -/
theorem dsHead_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa (.block (sqBases ++ [movi .x3 1, sth .x3 sCnt])) s fun t =>
      G I m₀ (Wk I.k) c t ∧ Frm I.B (hdrW ++ [(8 * sCnt, 8)]) s.mem t.mem ∧
      t.gpr .x10 = off I.B (slot (Wk I.k) wX4) ∧ t.gpr .x11 = off I.B (slot (Wk I.k) wS) ∧
      t.gpr .x12 = BitVec.ofNat 64 (Wk I.k) ∧ t.gpr .x7 = 0 ∧ t.gpr .x3 = BitVec.ofNat 64 1 ∧
      word t.mem I.B (8 * sCnt) = BitVec.ofNat 64 1 ∧
      Keep [.x3, .x4, .x7, .x9, .x10, .x11, .x12, .x16] s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv : vk I.k < 200 := by simp only [vk]; omega_using [hk2]
  show WP isa (.block (setWid ++ (ws ++ (base wX4 .x10 ++ (base wS .x9 ++ ([mov .x11 .x9, movi .x7 0, movi .x3 1] ++
    [sth .x3 sCnt])))))) s _
  rw [WP.block_append_iff]
  refine WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ws_ok g₁.ws.scr g₁.ws.x0 g₁.ws.h256 g₁.ws.hw g₁.ws.hS) fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ => ?_
  have x0₂ : s₂.gpr .x0 = I.B := (k₂.gpr .x0 (by decide)).trans g₁.ws.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok wX4 .x10 x0₂ h11) fun s₃ ⟨⟨h10, m₃, _⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok wS .x9 ((k₃.gpr .x0 (by decide)).trans x0₂) ((k₃.gpr .x11 (by decide)).trans h11))
    fun s₄ ⟨⟨h9, m₄, _⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x7, .x11] (Q := fun t => t.gpr .x11 = s₄.gpr .x9 ∧ t.gpr .x7 = 0 ∧
      t.gpr .x3 = BitVec.ofNat 64 1 ∧ t.mem = s₄.mem) (by brun) (by decide) (by decide) (by decide +kernel))
    fun s₅ ⟨⟨h11₅, h7₅, h3₅, m₅⟩, k₅⟩ => ?_
  have m5 : s₅.mem = s₁.mem := by rw [m₅, m₄, m₃, m₂]
  have g₅ : G I m₀ (Wk I.k) c s₅ := g₁.same m5 ((((k₂.trans k₃).trans k₄).trans k₅)) (by decide)
  refine WP.mono (sthOwn_ok g₅ (sl := sCnt) ⟨by decide, by decide, by decide⟩ .x3) fun t ⟨gt, ft, wt, kt⟩ => ?_
  have K := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans kt
  refine ⟨gt, (f₁.mono fun r hr => List.mem_append_left _ hr).trans (by
      rw [← m5]; exact ft.mono fun r hr => List.mem_append_right _ hr), ?_, ?_, ?_, ?_, ?_, by rw [wt, h3₅],
    K.mono⟩
  · rw [kt.get .x10, k₅.get .x10, k₄.get .x10]; exact h10
  · rw [kt.get .x11, h11₅, h9]
  · rw [kt.get .x12, k₅.get .x12, k₄.get .x12, k₃.get .x12, h12]
  · rw [kt.get .x7, h7₅]
  · rw [kt.get .x3, h3₅]

abbrev dsRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The ranges `digits` writes: the header, `sCnt`, the remainder and the root. -/
abbrev dsRanges (W : Nat) : List (Nat × Nat) :=
  hdrW ++ [(8 * sCnt, 8), (slot W wX4, 8 * W), (slot W wS, 8 * W)]

/-- `digits`: the `k - 1` digits after the first (`W = 2 k`), from `DV` after one digit to `DV` after `k`, for
`s₀` (in `sS0`) at least `2^63` and `v` (in `sV`) its reciprocal. -/
theorem digits_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa digits s fun t => G I m₀ (Wk I.k) c t ∧ Frm I.B (dsRanges (Wk I.k)) s.mem t.mem ∧ Keep dsRegs s t ∧
      ∀ Xn, 2 ^ 63 ≤ (word s.mem I.B (8 * sS0)).toNat →
        (word s.mem I.B (8 * sV)).toNat = (2 ^ 128 - 1) / (word s.mem I.B (8 * sS0)).toNat - 2 ^ 64 →
        DV s.mem I.B (slot (Wk I.k) wX4) (slot (Wk I.k) wS) (Wk I.k) (Wk I.k / 2) 1 Xn
          (word s.mem I.B (8 * sS0)).toNat →
        DV t.mem I.B (slot (Wk I.k) wX4) (slot (Wk I.k) wS) (Wk I.k) (Wk I.k / 2) (Wk I.k / 2) Xn
          (word s.mem I.B (8 * sS0)).toNat := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv : vk I.k < 200 := by simp only [vk]; omega_using [hk2]
  have hv1 : 1 ≤ vk I.k := by simp only [vk]; omega_using []
  have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have qS : slot (Wk I.k) wS = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
  have q16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
  have cS0 : 8 * sS0 = 240 := rfl
  have cV : 8 * sV = 200 := rfl
  have cC : 8 * sCnt = 208 := rfl
  generalize hWk : Wk I.k = W at *
  unfold digits
  refine WP.seq (WP.mono (dsHead_ok h L) fun u ⟨gu, fu, u10, u11, u12, u7, u3, uc, uk⟩ => ?_)
  rw [hWk] at gu u10 u11 u12
  have hn := gu.ws.scr.nowrap
  have hZ := gu.ws.hZ
  -- Words of the header the digits read.
  have fS0 : ∀ {m m' : Mem}, Frm I.B (dsRanges W) m m' → word m' I.B (8 * sS0) = word m I.B (8 * sS0) ∧
      word m' I.B (8 * sV) = word m I.B (8 * sV) := fun f => by
    refine ⟨f.word_eq (fun r hr => ?_) (by omega_using [cS0]), f.word_eq (fun r hr => ?_) (by omega_using [cV])⟩ <;>
    · simp only [dsRanges, hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn, sS0, sV, sCnt] <;> omega_arith
  have fU : Frm I.B (dsRanges W) s.mem u.mem := fu.mono fun r hr => by
    simp only [dsRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with hr | rfl
    · exact .inl hr
    · exact .inr (.inl rfl)
  obtain ⟨uS0, uV⟩ := fS0 fU
  let Inv : Nat → State → Prop := fun i t => G I m₀ W c t ∧ Frm I.B (dsRanges W) u.mem t.mem ∧ Keep digRegs u t ∧
    word t.mem I.B (8 * sCnt) = BitVec.ofNat 64 (i + 1) ∧
    ∀ Xn, 2 ^ 63 ≤ (word u.mem I.B (8 * sS0)).toNat →
      (word u.mem I.B (8 * sV)).toNat = (2 ^ 128 - 1) / (word u.mem I.B (8 * sS0)).toNat - 2 ^ 64 →
      DV u.mem I.B (slot W wX4) (slot W wS) W (W / 2) 1 Xn (word u.mem I.B (8 * sS0)).toNat →
      DV t.mem I.B (slot W wX4) (slot W wS) W (W / 2) (i + 1) Xn (word u.mem I.B (8 * sS0)).toNat
  have hRS : slot W wX4 + 8 * W ≤ slot W wS ∨ slot W wS + 8 * W ≤ slot W wX4 := by omega_using [qX, qS]
  refine WP.mono (count_loop (body := digit) (cr := .x3) (n := W / 2 - 1) (by omega_using [hv1, hW]) Inv
    (fun i hi t ⟨gt, ft, kt, ct, vt⟩ => ?_) ⟨gu, Frm.refl _ _ _, Keep.refl _ _, uc, fun _ _ _ h => h⟩)
    fun t ⟨gt, ft, kt, _, vt⟩ => ⟨gt, fU.trans ft, (uk.trans kt).mono, fun Xn hd hv h1 => ?_⟩
  · -- One digit.
    have t7 : t.gpr .x7 = 0 := by rw [kt.get .x7, u7]
    have t10 : t.gpr .x10 = off I.B (slot W wX4) := by rw [kt.get .x10, u10]
    have t11 : t.gpr .x11 = off I.B (slot W wS) := by rw [kt.get .x11, u11]
    have t12 : t.gpr .x12 = BitVec.ofNat 64 W := by rw [kt.get .x12, u12]
    obtain ⟨tS0, tV⟩ := fS0 ft
    refine WP.mono (digit_ok (eR := slot W wX4) (eS := slot W wS) (W := W) (m := i + 1) gt.ws.scr gt.ws.x0 t7 t10
      t11 t12 ct (by omega_using []) (by omega_using [hi]) (by omega_using [hv, hW]) (by omega_using [q16, hZ]) (by omega_using [qX, q16, hZ]) (by omega_using [qX]) (by omega_using [qS, q16, hZ]) (by omega_using [qS]) hRS)
      fun t' ⟨k', x3', mid, y, hout, hm, hval⟩ => ?_
    have e1 : slot W wS + 8 * (W / 2 - (i + 1) - 1) = slot W wS + 8 * (W / 2 - (i + 1)) - 8 := by omega_using [hi]
    rw [e1] at hm
    -- The memory: the window, the root's word and `sCnt`.
    have F : Frm I.B [(slot W wX4, 8 * W), (slot W wS, 8 * W), (8 * sCnt, 8)] t.mem t'.mem := by
      rw [hm]
      refine ((Frm.of_outside hout (List.mem_singleton_self _)).widen fun r hr => ?_).trans
        (((Frm.of_outside (writeW_outside _ I.B y (by omega_using [hv, hW, qS])) (List.mem_singleton_self _)).widen fun r hr => ?_).trans
          (Frm.of_outside (writeW_outside _ I.B _ (by omega_using [cC])) (by simp)))
      · rw [List.mem_singleton.mp hr]; exact ⟨(slot W wX4, 8 * W), by simp, by dsimp only; omega_using [], by dsimp only; omega_using [hi]⟩
      · rw [List.mem_singleton.mp hr]; exact ⟨(slot W wS, 8 * W), by simp, by dsimp only; omega_using [hi], by dsimp only; omega_using [hW]⟩
    have g' : G I m₀ W c t' := gt.frmOwn (sl := sCnt) (rs := [(slot W wX4, 8 * W), (slot W wS, 8 * W)])
      ⟨by decide, by decide, by decide⟩ F (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;>
        dsimp only <;> omega_arith) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;>
        dsimp only <;> omega_arith) k' (by decide)
    refine ⟨⟨g', ft.trans (F.mono fun r hr => by
        simp only [dsRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl <;> simp), kt.trans k' |>.mono, by rw [hm, word_writeW_self], fun Xn hd hv h1 => ?_⟩, ?_⟩
    · have dv := dv_step (m := i + 1) (k := W / 2) (mid := mid) (y := y) (by omega_using [hW]) (by omega_using []) (by omega_using [hi])
        (word u.mem I.B (8 * sS0)).isLt (by omega_arith) (by omega_arith) (by omega_using [qX, qS]) (vt Xn hd hv h1) hout
        fun Sv R P q a b cc dd e f => hval Sv R P q a b cc (by rw [tS0]; exact dd) (by rw [tS0]; exact hd) e f
          (by rw [tV, tS0]; exact hv)
      refine dv.congr (by omega_using [hi]) (fun j hj => ?_) (fun j hj => ?_) <;>
        rw [hm, (writeW_outside _ I.B _ (by omega_using [cC])).word (by omega_arith) (by omega_arith)]
    · rw [x3', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hv, hW])]; omega_using [hi]
  · have := vt Xn (by rw [uS0]; exact hd) (by rw [uV, uS0]; exact hv) (by
      rw [uS0]; refine h1.congr (by omega_using [hW]) (fun j hj => ?_) (fun j hj => ?_) <;>
        exact Frm.hdr_word fu (by omega_arith) (by omega_arith) (by simp only [List.mem_singleton]; rintro r rfl; dsimp only; omega_arith))
    rw [show W / 2 - 1 + 1 = W / 2 by omega_using [hW], uS0] at this
    exact this

/-! ## Normalization -/

/-- The index of the highest nonzero value of `f` below `i`, 0 if none. -/
def hiIdx (f : Nat → BitVec 64) : Nat → Nat
  | 0 => 0
  | i + 1 => if f i = 0 then hiIdx f i else i

/-- The last nonzero of `f`'s first `i` values (0 where there is none). -/
def topOf (f : Nat → BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | i + 1 => if f i = 0 then topOf f i else f i

/-- Whether any of `f`'s first `i` values is nonzero. -/
def nzOf (f : Nat → BitVec 64) : Nat → Bool
  | 0 => false
  | i + 1 => nzOf f i || decide (f i ≠ 0)

theorem topOf_hi (f : Nat → BitVec 64) : ∀ {k}, 1 ≤ k → topOf f k = f (hiIdx f k)
  | 0, h => absurd h (by decide)
  | 1, _ => by
    simp only [topOf, hiIdx]
    by_cases hz : f 0 = 0
    · rw [ite_eq_left hz, ite_eq_left hz, hz]
    · rw [ite_eq_right hz, ite_eq_right hz]
  | k + 2, _ => by
    simp only [topOf, hiIdx]
    by_cases hz : f (k + 1) = 0
    · rw [ite_eq_left hz, ite_eq_left hz]
      exact topOf_hi f (k := k + 1) (by omega_using [])
    · rw [ite_eq_right hz, ite_eq_right hz]

/-- A number of `i` words is below `2^(64 (hiIdx + 1))`, and at least `2^(64 hiIdx)` if not zero; it is not
zero exactly where a word is not. -/
theorem hiIdx_spec (m : Mem) (B : Addr) (d : Nat) : ∀ i,
    hiIdx (fun j => word m B (d + 8 * j)) i ≤ i - 1 ∧
    wv m B d i < 2 ^ (64 * (hiIdx (fun j => word m B (d + 8 * j)) i + 1)) ∧
    (0 < wv m B d i → 2 ^ (64 * hiIdx (fun j => word m B (d + 8 * j)) i) ≤ wv m B d i) ∧
    (nzOf (fun j => word m B (d + 8 * j)) i = decide (wv m B d i ≠ 0))
  | 0 => by simp [hiIdx, wv, nzOf]
  | i + 1 => by
    obtain ⟨ih1, ih2, ih3, ih4⟩ := hiIdx_spec m B d i
    rw [wv]
    simp only [hiIdx, nzOf]
    rw [ih4]
    have l := wv_lt m B d i
    by_cases hz : word m B (d + 8 * i) = 0
    · simp only [hz, ite_true, ne_eq, not_true_eq_false, decide_false, Bool.or_false]
      exact ⟨by omega_using [ih1], ih2, ih3, rfl⟩
    · simp only [hz, ite_false]
      have hp : 0 < (word m B (d + 8 * i)).toNat :=
        Nat.pos_of_ne_zero fun e => hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      have lw := (word m B (d + 8 * i)).isLt
      have hpos : 0 < 2 ^ (64 * i) * (word m B (d + 8 * i)).toNat := Nat.mul_pos (Nat.two_pow_pos _) hp
      refine ⟨by omega_using [], ?_, fun _ => ?_, ?_⟩
      · have : wv m B d i + 2 ^ (64 * i) * (word m B (d + 8 * i)).toNat < 2 ^ (64 * i) * 2 ^ 64 := by
          have := Nat.mul_le_mul_left (2 ^ (64 * i)) (show (word m B (d + 8 * i)).toNat + 1 ≤ 2 ^ 64 by omega_using [])
          rw [Nat.mul_add, Nat.mul_one] at this; omega_using [l, this]
        rwa [← Nat.pow_add, show 64 * i + 64 = 64 * (i + 1) by omega_using []] at this
      · have := Nat.le_mul_of_pos_right (2 ^ (64 * i)) hp; omega_using [this]
      · simp only [ne_eq, hz, not_false_eq_true, decide_true, Bool.or_true]
        exact (decide_eq_true (by omega_using [hpos])).symm

theorem sel_mask' (a b : BitVec 64) (c : Bool) : a ^^^ ((a ^^^ b) &&& mask c) = if c then b else a := by
  rw [BitVec.xor_comm a b]; exact sel_mask a b c

/-- The scan's body. -/
abbrev scanBody : List Instr :=
  [ld .x3 .x16, .subs .x .x4 .x7 .x3, .adc .x .x4 .x7 .x7, .subImm .x .x4 .x4 1,
    .logic .eor .x .x13 .x5 .x8, .logic .and .x .x13 .x13 .x4, .logic .eor .x .x5 .x5 .x13,
    .logic .eor .x .x13 .x6 .x3, .logic .and .x .x13 .x13 .x4, .logic .eor .x .x6 .x6 .x13,
    .logic .orr .x .x9 .x9 .x4, .addImm .x .x8 .x8 1, next .x16]

abbrev scanRegs : List Reg := [.x3, .x4, .x5, .x6, .x8, .x9, .x13, .x14, .x16]

/-- The scan of the `n` words at `x16`: the index of the top nonzero (`x5`), that word (`x6`), and whether any is
nonzero (`x9`, a mask). -/
theorem scan_ok {s : State} {B : Addr} {Z d n : Nat} (hs : Scr s B Z) (h16 : s.gpr .x16 = off B d)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 n) (h7 : s.gpr .x7 = 0) (h5 : s.gpr .x5 = 0) (h6 : s.gpr .x6 = 0)
    (h8 : s.gpr .x8 = 0) (h9 : s.gpr .x9 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hZ : d + 8 * n ≤ Z) :
    WP isa (countLoop .x14 scanBody) s fun t =>
      t.mem = s.mem ∧ t.gpr .x5 = BitVec.ofNat 64 (hiIdx (fun j => word s.mem B (d + 8 * j)) n) ∧
      t.gpr .x6 = topOf (fun j => word s.mem B (d + 8 * j)) n ∧
      t.gpr .x9 = mask (nzOf (fun j => word s.mem B (d + 8 * j)) n) ∧ Keep scanRegs s t := by
  have hnw := hs.nowrap
  generalize hf : (fun j => word s.mem B (d + 8 * j)) = f
  let Inv : Nat → State → Prop := fun i t => t.mem = s.mem ∧ t.gpr .x16 = off B (d + 8 * i) ∧
    t.gpr .x8 = BitVec.ofNat 64 i ∧ t.gpr .x5 = BitVec.ofNat 64 (hiIdx f i) ∧ t.gpr .x6 = topOf f i ∧
    t.gpr .x9 = mask (nzOf f i) ∧ Keep scanRegs s t
  refine WP.mono (wp_countdown (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv (fun i hi t ⟨jm, j16, j8, j5, j6, j9, jk⟩ _ => ?_)
    ⟨rfl, by rw [h16]; rfl, h8, h5, h6, by rw [h9, show nzOf f 0 = false from rfl]; decide, Keep.refl _ _⟩ h14) fun t ⟨tm, _, _, t5, t6, t9, tk⟩ => ⟨tm, t5, t6, t9, tk⟩
  have hst := hs.congr jk.wr
  have t7 : t.gpr .x7 = 0 := (jk.gpr .x7 (by decide)).trans h7
  have wa : word t.mem B (d + 8 * i) = f i := by rw [jm, ← hf]
  refine WP.mono (WP.keep scanRegs (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .x16 = off B (d + 8 * (i + 1)) ∧
      t'.gpr .x8 = BitVec.ofNat 64 (i + 1) ∧
      t'.gpr .x5 = (if decide (f i ≠ 0) then BitVec.ofNat 64 i else t.gpr .x5) ∧
      t'.gpr .x6 = (if decide (f i ≠ 0) then f i else t.gpr .x6) ∧
      t'.gpr .x9 = mask (nzOf f i || decide (f i ≠ 0)) ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1) (by
    brun [j16, j8, j9, t7, wa, hst.ld (show d + 8 * i + 8 ≤ Z by omega_using [hZ, hi]), nz_mask, sel_mask', mask_or', off_add,
      BitVec.ofNat_add_ofNat, show d + 8 * i + 8 = d + 8 * (i + 1) by omega_using []])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨m', a16, a8, a5, a6, a9, a14⟩, k'⟩ =>
      ⟨⟨by rw [m', jm], a16, a8, ?_, ?_, a9, (jk.trans k').mono⟩, a14⟩
  · rw [a5, j5]; simp only [hiIdx]
    by_cases hz : f i = 0 <;> simp only [hz, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
      Bool.false_eq_true, ↓reduceIte]
  · rw [a6, j6]; simp only [topOf]
    by_cases hz : f i = 0 <;> simp only [hz, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
      Bool.false_eq_true, ↓reduceIte]

theorem exec_clz' (s : State) (d n : Reg) :
    exec (Instr.clz .x d n) s = some (s.write .x d (s.gpr n).clz) := by
  simp [exec, State.read]

/-- The normalizing shift: `64 (W - 1 - hi) + clz(top)` made even, 0 where the number is zero. -/
theorem c2_val {W hi : Nat} (h : hi < W) (hW : W < 2 ^ 24) (top : BitVec 64) (nz : Bool) :
    ((BitVec.ofNat 64 W - BitVec.ofNat 64 hi - 1#64) <<< 6 + top.clz) >>> 1 <<< 1 &&& mask nz =
      BitVec.ofNat 64 (if nz = true then (64 * (W - 1 - hi) + top.clz.toNat) / 2 * 2 else 0) := by
  have hc : top.clz.toNat ≤ 64 := by
    have := BitVec.clz_le (x := top); rw [BitVec.le_def] at this; simpa using this
  apply BitVec.eq_of_toNat_eq
  rw [and_mask_toNat']
  have e1 : (BitVec.ofNat 64 W - BitVec.ofNat 64 hi - 1#64).toNat = W - 1 - hi := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_using [h, hW]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, e1, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  cases nz <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_mul, Nat.one_mul, Bool.false_eq_true,
    ↓reduceIte, BitVec.toNat_ofNat] <;> omega_using []

theorem nShift_ok {s : State} {W hi : Nat} {top : BitVec 64} {nz : Bool} (h12 : s.gpr .x12 = BitVec.ofNat 64 W)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 hi) (h6 : s.gpr .x6 = top) (h9 : s.gpr .x9 = mask nz) (hhi : hi < W)
    (hW : W < 2 ^ 24) :
    WP isa (.block [.clz .x .x3 .x6, .sub .x .x4 .x12 .x5, .subImm .x .x4 .x4 1, .lsl .x .x4 .x4 6,
      .add .x .x4 .x4 .x3, .lsr .x .x4 .x4 1, .lsl .x .x4 .x4 1, .logic .and .x .x4 .x4 .x9]) s fun t =>
      (t.gpr .x4 = BitVec.ofNat 64 (if nz then (64 * (W - 1 - hi) + top.clz.toNat) / 2 * 2 else 0) ∧
        t.mem = s.mem) ∧ Keep [.x3, .x4] s t := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [exec_clz', h12, h5, h6, h9, c2_val hhi hW]

/-- `norm`'s head: the bases, the scan's start. -/
theorem nHead_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa (.block (setWid ++ ws ++ base wX4 .x16 ++ [movi .x7 0, movi .x5 0, movi .x6 0, movi .x8 0, movi .x9 0,
      mov .x14 .x12])) s fun t =>
      G I m₀ (Wk I.k) c t ∧ Frm I.B hdrW s.mem t.mem ∧ t.gpr .x16 = off I.B (slot (Wk I.k) wX4) ∧
      t.gpr .x12 = BitVec.ofNat 64 (Wk I.k) ∧ t.gpr .x14 = BitVec.ofNat 64 (Wk I.k) ∧ t.gpr .x7 = 0 ∧
      t.gpr .x5 = 0 ∧ t.gpr .x6 = 0 ∧ t.gpr .x8 = 0 ∧ t.gpr .x9 = 0 ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x14, .x16] s t := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_
  refine WP.mono (ws_ok g₁.ws.scr g₁.ws.x0 g₁.ws.h256 g₁.ws.hw g₁.ws.hS) fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ => ?_
  have x0₂ : s₂.gpr .x0 = I.B := (k₂.gpr .x0 (by decide)).trans g₁.ws.x0
  refine WP.mono (base_ok wX4 .x16 x0₂ h11) fun s₃ ⟨⟨h16, m₃, _⟩, k₃⟩ => ?_
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x14] (Q := fun t => t.gpr .x7 = 0 ∧ t.gpr .x5 = 0 ∧
      t.gpr .x6 = 0 ∧ t.gpr .x8 = 0 ∧ t.gpr .x9 = 0 ∧ t.gpr .x14 = s₃.gpr .x12 ∧ t.mem = s₃.mem) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨t7, t5, t6, t8, t9, t14, mt⟩, kt⟩ => ?_
  have m4 : t.mem = s₁.mem := by rw [mt, m₃, m₂]
  have x12 : s₃.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := by rw [k₃.get .x12, h12]
  exact ⟨g₁.same m4 ((k₂.trans k₃).trans kt) (by decide), by rw [m4]; exact f₁,
    by rw [kt.get .x16]; exact h16, by rw [kt.get .x12, x12], by rw [t14, x12], t7, t5, t6, t8, t9,
    (((k₁.trans k₂).trans k₃).trans kt).mono⟩

/-- A word below `2^64`, not zero, normalized by its leading zeros. -/
theorem clz_norm {x : BitVec 64} (hx : x ≠ 0) :
    x.clz.toNat ≤ 63 ∧ 2 ^ 63 ≤ x.toNat * 2 ^ x.clz.toNat ∧ x.toNat * 2 ^ x.clz.toNat < 2 ^ 64 := by
  have h1 := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (w := 64) (by decide) hx
  have h2 := BitVec.toNat_lt_two_pow_sub_clz (x := x)
  have h3 : x.clz.toNat < 64 := by
    have := BitVec.clz_lt_iff_ne_zero.mpr hx; rw [BitVec.lt_def] at this; simpa using this
  refine ⟨by omega_using [h3], ?_, ?_⟩
  · calc 2 ^ 63 = 2 ^ (64 - 1 - x.clz.toNat) * 2 ^ x.clz.toNat := by rw [← Nat.pow_add]; congr 1; omega_using [h3]
      _ ≤ x.toNat * 2 ^ x.clz.toNat := Nat.mul_le_mul_right _ h1
  · calc x.toNat * 2 ^ x.clz.toNat < 2 ^ (64 - x.clz.toNat) * 2 ^ x.clz.toNat :=
          Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega_using [h3]

/-- The normalized number: `X 4^c`, `c` half the shift, at least `2^(64 W - 2)` where `X ≠ 0`, the shift within the
width. -/
theorem norm_val {mm : Mem} {B : Addr} {d W : Nat} (hW : 1 ≤ W) {f : Nat → BitVec 64}
    (hf : (fun j => word mm B (d + 8 * j)) = f) {c2 : Nat}
    (hc2 : c2 = if nzOf f W = true then (64 * (W - 1 - hiIdx f W) + (topOf f W).clz.toNat) / 2 * 2 else 0) :
    c2 < 64 * W ∧ c2 % 2 = 0 ∧ wv mm B d W * 2 ^ c2 < 2 ^ (64 * W) ∧
      (wv mm B d W ≠ 0 → 2 ^ (64 * W - 2) ≤ wv mm B d W * 2 ^ c2) ∧ (wv mm B d W = 0 → c2 = 0) := by
  obtain ⟨s1, s2, s3, s4⟩ := hiIdx_spec mm B d W
  rw [hf] at s1 s2 s3 s4
  have hX := wv_lt mm B d W
  by_cases hz : wv mm B d W = 0
  · have : nzOf f W = false := by rw [s4]; simp [hz]
    have hc : c2 = 0 := by rw [hc2, this]; rfl
    rw [hc, hz]
    exact ⟨by omega_using [hW], rfl, by simp, fun h => absurd rfl h, fun _ => rfl⟩
  · have hnz : nzOf f W = true := by rw [s4]; simp [hz]
    have ht := topOf_hi f (k := W) hW
    have hc : c2 = (64 * (W - 1 - hiIdx f W) + (topOf f W).clz.toNat) / 2 * 2 := by rw [hc2, hnz]; rfl
    rw [ht] at hc
    generalize hH : hiIdx f W = H at s1 s2 s3 hc
    have hfH : f H = word mm B (d + 8 * H) := by rw [← hf]
    rw [hfH] at hc
    subst hc
    have hT := top_word_div (mm := mm) (B := B) (p := d) (hi := H) (W := W) (by omega_using [hW, s1]) s2
    have htop : word mm B (d + 8 * H) ≠ 0 := by
      intro e
      rw [e] at hT
      have := s3 (by omega_using [hz])
      have := Nat.lt_of_div_eq_zero (Nat.two_pow_pos _) hT.symm
      omega_arith
    obtain ⟨z1, z2, z3⟩ := clz_norm htop
    rw [hT] at z2 z3
    obtain ⟨b1, b2⟩ := norm_bounds (W := W) (hi := H) rfl (by omega_using [hW, s1]) z1 z2 z3
    refine ⟨by omega_using [hW, z1], by omega_using [], b2, fun _ => b1, fun h => absurd h hz⟩

theorem shr1_ofNat {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c >>> 1 = BitVec.ofNat 64 (c / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega_using [hc]

theorem ones_xor_mask (b : Bool) : (0 : BitVec 64) - 1#64 ^^^ mask b = mask (!b) := by cases b <;> rfl

/-- The ranges `norm` writes. -/
abbrev nmRanges (W : Nat) : List (Nat × Nat) := hdrW ++ [(8 * sT1, 8), (8 * sC, 8), (8 * sZ, 8), (slot W wX4, 8 * W)]

/-- `norm`'s head: the scan, `c₂`, `c` and the mask of `X = 0`. -/
abbrev nPre : List (Prog isa) := [
  .block (setWid ++ ws ++ base wX4 .x16 ++ [movi .x7 0, movi .x5 0, movi .x6 0, movi .x8 0, movi .x9 0, mov .x14 .x12]),
  countLoop .x14 [ld .x3 .x16, .subs .x .x4 .x7 .x3, .adc .x .x4 .x7 .x7, .subImm .x .x4 .x4 1,
    .logic .eor .x .x13 .x5 .x8, .logic .and .x .x13 .x13 .x4, .logic .eor .x .x5 .x5 .x13,
    .logic .eor .x .x13 .x6 .x3, .logic .and .x .x13 .x13 .x4, .logic .eor .x .x6 .x6 .x13,
    .logic .orr .x .x9 .x9 .x4, .addImm .x .x8 .x8 1, next .x16],
  .block [.clz .x .x3 .x6, .sub .x .x4 .x12 .x5, .subImm .x .x4 .x4 1, .lsl .x .x4 .x4 6, .add .x .x4 .x4 .x3,
    .lsr .x .x4 .x4 1, .lsl .x .x4 .x4 1, .logic .and .x .x4 .x4 .x9, sth .x4 sT1, .lsr .x .x3 .x4 1, sth .x3 sC,
    .subImm .x .x13 .x7 1, .logic .eor .x .x13 .x13 .x9, sth .x13 sZ]]

theorem norm_eq : norm = seqs (nPre ++ shiftBy wX4 true true sT1) := rfl

/-- `nPre`'s frame. -/
abbrev npRanges : List (Nat × Nat) := hdrW ++ [(8 * sT1, 8), (8 * sC, 8), (8 * sZ, 8)]

theorem nPre_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa (seqs nPre) s fun t => ∃ c2, G I m₀ (Wk I.k) c t ∧ Frm I.B npRanges s.mem t.mem ∧ Keep dsRegs s t ∧
      word t.mem I.B (8 * sT1) = BitVec.ofNat 64 c2 ∧ word t.mem I.B (8 * sC) = BitVec.ofNat 64 (c2 / 2) ∧
      word t.mem I.B (8 * sZ) = mask (decide (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = 0)) ∧
      wv t.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) ∧
      c2 < 64 * Wk I.k ∧ c2 % 2 = 0 ∧ wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) * 2 ^ c2 < 2 ^ (64 * Wk I.k) ∧
      (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) ≠ 0 →
        2 ^ (64 * Wk I.k - 2) ≤ wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) * 2 ^ c2) := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv : vk I.k < 200 := by simp only [vk]; omega_using [hk2]
  have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have q16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
  simp only [seqs]
  refine WP.seq (WP.mono (nHead_ok h L) fun s₁ ⟨g₁, f₁, x16, x12, x14, x7, x5, x6, x8, x9, k₁⟩ => ?_)
  have hn := g₁.ws.scr.nowrap
  have hZ := g₁.ws.hZ
  refine WP.seq (WP.mono (scan_ok g₁.ws.scr x16 x14 x7 x5 x6 x8 x9 (by omega_using [hW]) (by omega_using [hW, hv]) (by omega_using [qX, q16, hZ]))
    fun s₂ ⟨m₂, a5, a6, a9, k₂⟩ => ?_)
  generalize hf : (fun j => word s₁.mem I.B (slot (Wk I.k) wX4 + 8 * j)) = f at a5 a6 a9
  have g₂ : G I m₀ (Wk I.k) c s₂ := g₁.same m₂ k₂ (by decide)
  have nv := norm_val (mm := s₁.mem) (B := I.B) (d := slot (Wk I.k) wX4) (W := Wk I.k) (by omega_using [hW]) hf rfl
  generalize hc2 : (if nzOf f (Wk I.k) = true then
    (64 * (Wk I.k - 1 - hiIdx f (Wk I.k)) + (topOf f (Wk I.k)).clz.toNat) / 2 * 2 else 0) = c2 at nv
  obtain ⟨c2l, c2e, c2x, c2b, c2z⟩ := nv
  have hX1 : wv s₁.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) :=
    Frm.hdrW_wv f₁ (by omega_using [qX]) (by omega_using [hW, hv, qX])
  rw [hX1] at c2x c2b c2z
  have hnz : nzOf f (Wk I.k) = decide (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) ≠ 0) := by
    rw [← hf, (hiIdx_spec s₁.mem I.B _ _).2.2.2, hX1]
  obtain ⟨hhi, -, -, -⟩ := hiIdx_spec s₁.mem I.B (slot (Wk I.k) wX4) (Wk I.k)
  rw [hf] at hhi
  show WP isa (.block ([.clz .x .x3 .x6, .sub .x .x4 .x12 .x5, .subImm .x .x4 .x4 1, .lsl .x .x4 .x4 6,
    .add .x .x4 .x4 .x3, .lsr .x .x4 .x4 1, .lsl .x .x4 .x4 1, .logic .and .x .x4 .x4 .x9] ++ ([sth .x4 sT1] ++
    ([.lsr .x .x3 .x4 1] ++ ([sth .x3 sC] ++ ([.subImm .x .x13 .x7 1, .logic .eor .x .x13 .x13 .x9] ++
    [sth .x13 sZ])))))) s₂ _
  rw [WP.block_append_iff]
  refine WP.mono (nShift_ok (W := Wk I.k) (by rw [k₂.get .x12]; exact x12) a5 a6 a9 (by omega_using [hW, hhi]) (by omega_using [hW, hv]))
    fun s₃ ⟨⟨b4, m₃⟩, k₃⟩ => ?_
  rw [hc2] at b4
  have g₃ : G I m₀ (Wk I.k) c s₃ := g₂.same m₃ k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sthOwn_ok g₃ (sl := sT1) ⟨by decide, by decide, by decide⟩ .x4) fun s₄ ⟨g₄, f₄, w₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (c2 / 2) ∧ t.mem = s₄.mem)
    (by brun [k₄.get .x4, b4, shr1_ofNat (show c2 < 2 ^ 64 by omega_using [hW, hv, c2l])]) (by decide) (by decide) (by decide +kernel))
    fun s₅ ⟨⟨b3, m₅⟩, k₅⟩ => ?_
  have g₅ : G I m₀ (Wk I.k) c s₅ := g₄.same m₅ k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sthOwn_ok g₅ (sl := sC) ⟨by decide, by decide, by decide⟩ .x3) fun s₆ ⟨g₆, f₆, w₆, k₆⟩ => ?_
  rw [WP.block_append_iff]
  have x7₆ : s₆.gpr .x7 = 0 := by rw [k₆.get .x7, k₅.get .x7, k₄.get .x7, k₃.get .x7, k₂.get .x7, x7]
  have x9₆ : s₆.gpr .x9 = mask (nzOf f (Wk I.k)) := by
    rw [k₆.get .x9, k₅.get .x9, k₄.get .x9, k₃.get .x9, a9]
  refine WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x13 = mask (!nzOf f (Wk I.k)) ∧ t.mem = s₆.mem)
    (by brun [x7₆, x9₆, ones_xor_mask]) (by decide) (by decide) (by decide +kernel)) fun s₇ ⟨⟨b13, m₇⟩, k₇⟩ => ?_
  have g₇ : G I m₀ (Wk I.k) c s₇ := g₆.same m₇ k₇ (by decide)
  refine WP.mono (sthOwn_ok g₇ (sl := sZ) ⟨by decide, by decide, by decide⟩ .x13) fun s₈ ⟨g₈, f₈, w₈, k₈⟩ => ?_
  have hsT : sT1 = 29 := rfl
  have hsC : sC = 27 := rfl
  have hsZ : sZ = 31 := rfl
  have sep : ∀ {a b : Nat}, a < 32 → b < 32 → a ≠ b → ∀ r ∈ [(8 * b, 8)], 8 * a + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * a :=
    fun ha hb hab r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_using [hab]
  have wT1 : word s₈.mem I.B (8 * sT1) = BitVec.ofNat 64 c2 := by
    rw [f₈.word_eq (sep (by decide) (by decide) (by decide)) (by omega_using [hsT]), m₇,
      f₆.word_eq (sep (by decide) (by decide) (by decide)) (by omega_using [hsT]), m₅, w₄, b4]
  have hA : wv s₈.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) := by
    have o : ∀ {m m' : Mem} {sl : Nat}, sl < 32 → Frm I.B [(8 * sl, 8)] m m' →
        wv m' I.B (slot (Wk I.k) wX4) (Wk I.k) = wv m I.B (slot (Wk I.k) wX4) (Wk I.k) := fun hsl f =>
      f.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_using [qX, hsl]) (by omega_using [hW, hv, qX])
    rw [o (by decide) f₈, m₇, o (by decide) f₆, m₅, o (by decide) f₄, m₃, m₂, hX1]
  refine ⟨c2, g₈, ?_, ((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈)).mono, wT1, ?_,
    ?_, hA, c2l, c2e, c2x, c2b⟩
  · have r1 : ∀ {m m' : Mem}, m' = m → Frm I.B npRanges m m' := fun e => by rw [e]; exact Frm.refl _ _ _
    refine (f₁.mono fun r hr => List.mem_append_left _ hr).trans ((r1 m₂).trans ((r1 m₃).trans
      ((f₄.mono fun r hr => ?_).trans ((r1 m₅).trans ((f₆.mono fun r hr => ?_).trans ((r1 m₇).trans
      (f₈.mono fun r hr => ?_))))))) <;>
    · simp only [npRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      first | (rcases hr with hr | hr <;> simp [hr]) | simp [hr]
  · rw [f₈.word_eq (sep (by decide) (by decide) (by decide)) (by omega_using [hsC]), m₇, w₆, b3]
  · rw [w₈, b13, hnz]; simp

/-- `norm`: `X` (wide array `wX4`) times `4^c`, `c` into `sC`, at least `2^(64 W - 2)` where `X ≠ 0`, and `sZ` the
mask of `X = 0`. -/
theorem norm_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa norm s fun t => G I m₀ (vk I.k) c t ∧ Frm I.B (nmRanges (Wk I.k)) s.mem t.mem ∧ Keep dsRegs s t ∧
      word t.mem I.B (8 * sZ) = mask (decide (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = 0)) ∧
      ∃ cc, word t.mem I.B (8 * sC) = BitVec.ofNat 64 cc ∧ cc ≤ 32 * Wk I.k ∧
        wv t.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) * 4 ^ cc ∧
        (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) ≠ 0 →
          2 ^ (64 * Wk I.k - 2) ≤ wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) * 4 ^ cc) := by
  have hk1 := L.k1
  have hk2 := L.k2
  rw [norm_eq]
  refine wp_seqs_append (by simp) (by simp [shiftBy]) (WP.mono (nPre_ok h L)
    fun s₈ ⟨c2, g₈, f₈, k₈, wT1, wC, wZ, hA, c2l, c2e, c2x, c2b⟩ => ?_)
  have hn := g₈.ws.scr.nowrap
  have hZ := g₈.ws.hZ
  refine WP.mono (shiftBy_ok g₈ L true true (j := wX4) (by decide) (sl := sT1) (by decide) (by decide) (by decide) wT1
    (N := Wk I.k) rfl (by omega_using [c2l])) fun t ⟨gt, ft, vt, kt⟩ => ?_
  have e4 : 2 ^ c2 = 4 ^ (c2 / 2) := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]; congr 1; omega_using [c2e]
  refine ⟨gt, ?_, (k₈.trans kt).mono, ?_, c2 / 2, ?_, by omega_using [c2l], ?_, fun hX => ?_⟩
  · refine (f₈.mono fun r hr => ?_).trans (ft.mono fun r hr => ?_)
    · rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · refine List.mem_append_right _ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h <;> simp [h]
    · rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · refine List.mem_append_right _ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        simp [hr]
  · rw [stage_word ft (by decide) (by decide) (by decide), wZ]
  · rw [stage_word ft (by decide) (by decide) (by decide), wC]
  · rw [vt, hA, shV, ite_eq_left rfl, Nat.mod_eq_of_lt c2x, e4]
  · rw [← e4]; exact c2b hX

/-! ## The square root's tail -/

theorem wv_zero_iff (m : Mem) (B : Addr) (d : Nat) : ∀ n, wv m B d n = 0 ↔ ∀ j < n, word m B (d + 8 * j) = 0
  | 0 => by simp [wv]
  | n + 1 => by
    rw [wv, Nat.add_eq_zero_iff, wv_zero_iff m B d n, Nat.mul_eq_zero]
    have hp : 2 ^ (64 * n) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
    have hw : (word m B (d + 8 * n)).toNat = 0 ↔ word m B (d + 8 * n) = 0 :=
      ⟨fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl), fun h => by rw [h]; rfl⟩
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 hp
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        exacts [h1 j hj, hw.mp h2]
    · intro h
      exact ⟨fun j hj => h j (by omega_using [hj]), .inr (hw.mpr (h n (by omega_using [])))⟩

theorem or_zero' (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := BitVec.or_eq_zero_iff

/-- `countLoop .x14` of the OR of the `n` words at `x16` into `x9`. -/
theorem orAll_ok {s : State} {B : Addr} {Z d n : Nat} (hs : Scr s B Z) (h16 : s.gpr .x16 = off B d)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 n) (h9 : s.gpr .x9 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hZ : d + 8 * n ≤ Z) :
    WP isa (countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16]) s fun t =>
      t.mem = s.mem ∧ (t.gpr .x9 = 0 ↔ wv s.mem B d n = 0) ∧ Keep [.x3, .x9, .x14, .x16] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t => t.mem = s.mem ∧ t.gpr .x16 = off B (d + 8 * i) ∧
    (t.gpr .x9 = 0 ↔ ∀ j < i, word s.mem B (d + 8 * j) = 0) ∧ Keep [.x3, .x9, .x14, .x16] s t
  refine WP.mono (wp_countdown (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv (fun i hi t ⟨jm, j16, j9, jk⟩ _ => ?_)
    ⟨rfl, by rw [h16]; rfl, by simp [h9], Keep.refl _ _⟩ h14) fun t ⟨tm, _, t9, tk⟩ =>
      ⟨tm, t9.trans (wv_zero_iff _ _ _ _).symm, tk⟩
  have hst := hs.congr jk.wr
  refine WP.mono (WP.keep [.x3, .x9, .x14, .x16] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .x16 = off B (d + 8 * (i + 1)) ∧ t'.gpr .x9 = t.gpr .x9 ||| word s.mem B (d + 8 * i) ∧
      t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1) (by
    brun [j16, jm, hst.ld (show d + 8 * i + 8 ≤ Z by omega_using [hZ, hi]), off_add, show d + 8 * i + 8 = d + 8 * (i + 1) by omega_using []])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨m', a16, a9, a14⟩, k'⟩ =>
      ⟨⟨by rw [m', jm], a16, ?_, (jk.trans k').mono⟩, a14⟩
  rw [a9, or_zero', j9]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    exacts [h1 j hj, h2]
  · intro h
    exact ⟨fun j hj => h j (by omega_using [hj]), h i (by omega_using [])⟩

/-- `countLoop .x14` of the `n` words at `x16` and'ed with the mask `x15`. -/
theorem maskAll_ok {s : State} {B : Addr} {Z d n : Nat} {b : Bool} (hs : Scr s B Z) (h16 : s.gpr .x16 = off B d)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 n) (h15 : s.gpr .x15 = mask b) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hZ : d + 8 * n ≤ Z) :
    WP isa (countLoop .x14 [ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x16, next .x16]) s fun t =>
      wv t.mem B d n = b.toNat * wv s.mem B d n ∧ Outside B d (8 * n) s.mem t.mem ∧ Keep [.x3, .x14, .x16] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t => t.gpr .x16 = off B (d + 8 * i) ∧ Outside B d (8 * i) s.mem t.mem ∧
    (∀ j < n, word t.mem B (d + 8 * j) = if j < i then word s.mem B (d + 8 * j) &&& mask b
      else word s.mem B (d + 8 * j)) ∧ Keep [.x3, .x14, .x16] s t
  refine WP.mono (wp_countdown (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv (fun i hi t ⟨j16, jo, jw, jk⟩ _ => ?_)
    ⟨by rw [h16]; rfl, Outside.refl _ _ _ _, fun j _ => by simp, Keep.refl _ _⟩ h14) fun t ⟨_, tO, tw, tk⟩ =>
      ⟨?_, tO, tk⟩
  · have hst := hs.congr jk.wr
    have t15 : t.gpr .x15 = mask b := (jk.gpr .x15 (by decide)).trans h15
    have wi : word t.mem B (d + 8 * i) = word s.mem B (d + 8 * i) := by rw [jw i hi, ite_eq_right (Nat.lt_irrefl _)]
    refine WP.mono (WP.keep [.x3, .x14, .x16] (Q := fun t' =>
        t'.mem = t.mem.writeW (off B (d + 8 * i)) (word s.mem B (d + 8 * i) &&& mask b) ∧
        t'.gpr .x16 = off B (d + 8 * (i + 1)) ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1) (by
      brun [j16, t15, wi, hst.ld (show d + 8 * i + 8 ≤ Z by omega_using [hZ, hi]), hst.st (show d + 8 * i + 8 ≤ Z by omega_using [hZ, hi]), off_add,
        show d + 8 * i + 8 = d + 8 * (i + 1) by omega_using []])
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨m', a16, a14⟩, k'⟩ =>
        ⟨⟨a16, ?_, fun j hj => ?_, (jk.trans k').mono⟩, a14⟩
    · rw [m']; exact out_step _ jo (by omega_using [hZ, hnw, hi])
    · rw [m']
      rcases Nat.lt_or_ge j i with hj' | hj'
      · rw [(writeW_outside _ B _ (by omega_using [hZ, hnw, hi])).word (by omega_using [hj']) (by omega_using [hZ, hnw, hj]), jw j hj, ite_eq_left hj', ite_eq_left (by omega_using [hj'])]
      · rcases Nat.eq_or_lt_of_le hj' with rfl | hj''
        · rw [word_writeW_self, ite_eq_left (by omega_using [])]
        · rw [(writeW_outside _ B _ (by omega_using [hZ, hnw, hi])).word (by omega_using [hj'']) (by omega_using [hZ, hnw, hj]), jw j hj, ite_eq_right (by omega_using [hj']),
            ite_eq_right (by omega_using [hj''])]
  · have hw : ∀ j < n, word t.mem B (d + 8 * j) = word s.mem B (d + 8 * j) &&& mask b := fun j hj => by
      rw [tw j hj, ite_eq_left hj]
    cases b
    · rw [Bool.toNat_false, Nat.zero_mul]
      exact (wv_zero_iff _ _ _ _).mpr fun j hj => by rw [hw j hj, show mask false = 0 by decide]; exact BitVec.and_zero
    · rw [Bool.toNat_true, Nat.one_mul]
      exact wv_congr fun j hj => by rw [hw j hj, show mask true = BitVec.allOnes 64 by decide, BitVec.and_allOnes]

/-- What the square root writes: the header, its root and its remainder (wide). -/
abbrev sqR (W : Nat) : List (Nat × Nat) := [(0, 256), (slot W wS, 8 * (W + 2)), (slot W wX4, 8 * (W + 2))]

theorem frm_sq {B : Addr} {W : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (f : Frm B rs m m')
    (h : ∀ r ∈ rs, r.1 + r.2 ≤ 256 ∨ (slot W wS ≤ r.1 ∧ r.1 + r.2 ≤ slot W wS + 8 * (W + 2)) ∨
      (slot W wX4 ≤ r.1 ∧ r.1 + r.2 ≤ slot W wX4 + 8 * (W + 2))) : Frm B (sqR W) m m' :=
  f.widen fun r hr => by
    rcases h r hr with h | h | h
    · exact ⟨(0, 256), by simp, Nat.zero_le _, h⟩
    · exact ⟨(slot W wS, 8 * (W + 2)), by simp, h.1, h.2⟩
    · exact ⟨(slot W wX4, 8 * (W + 2)), by simp, h.1, h.2⟩

/-- The square root's front: `[wX4] = X` normalized by `4^c`, its root's digits and the remainder, where `X ≠ 0`. -/
theorem sqrtFront_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa (seqs [.block setWid, zeroA wS, norm, first, digits]) s fun t =>
      G I m₀ (Wk I.k) c t ∧ Frm I.B (sqR (Wk I.k)) s.mem t.mem ∧
      word t.mem I.B (8 * sZ) = mask (decide (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = 0)) ∧
      ∃ cc, word t.mem I.B (8 * sC) = BitVec.ofNat 64 cc ∧ cc ≤ 32 * Wk I.k ∧
        (wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) ≠ 0 → ∃ Sv R, wv t.mem I.B (slot (Wk I.k) wS) (Wk I.k) = Sv ∧
          wv t.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = R ∧ R ≤ 2 * Sv ∧
          Sv * Sv + R = wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) * 4 ^ cc) := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv : vk I.k < 200 := by simp only [vk]; omega_using [hk2]
  have hv1 : 1 ≤ vk I.k := by simp only [vk]; omega_using []
  have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have qS : slot (Wk I.k) wS = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
  have q16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
  have cH : 8 * sW = 48 ∧ 8 * sArr 0 = 64 ∧ 8 * sStride = 224 ∧ 8 * sCnt = 208 ∧ 8 * sS0 = 240 ∧
    8 * sV = 200 ∧ 8 * sT1 = 232 ∧ 8 * sC = 216 ∧ 8 * sZ = 248 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := cH
  simp only [seqs]
  refine WP.seq (WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  have hn := g₁.ws.scr.nowrap
  have hZ := g₁.ws.hZ
  refine WP.seq (WP.mono (zeroA_ok g₁.ws (j := wS) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  have hX₂ : wv s₂.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) := by
    rw [o₂.wv (by omega_using [qX, qS]) (by omega_using [hW, hv, qX]), Frm.hdrW_wv f₁ (by omega_using [qX]) (by omega_using [hW, hv, qX])]
  have hS₂ : wv s₂.mem I.B (slot (Wk I.k) wS) (Wk I.k) = 0 := (wv_prefix (a := Wk I.k) (b := 2) z₂ (Nat.two_pow_pos _)).1
  generalize hX : wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = X at hX₂
  refine WP.seq (WP.mono (norm_ok g₂ L) fun s₃ ⟨g₃, f₃, _, sZ₃, cc, sC₃, ccl, vX₃, lo₃⟩ => ?_)
  rw [hX₂] at sZ₃ vX₃ lo₃
  have hS₃ : wv s₃.mem I.B (slot (Wk I.k) wS) (Wk I.k) = 0 := by
    rw [f₃.wv_eq (fun r hr => by
      simp only [nmRanges, hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_using [hW, hv, qS]), hS₂]
  refine WP.seq (WP.mono (first_ok g₃ L hS₃) fun s₄ ⟨g₄, f₄, s0₄, v₄, dv₄⟩ => ?_)
  rw [vX₃] at s0₄ dv₄
  refine WP.mono (digits_ok g₄ L) fun s₅ ⟨g₅, f₅, _, dv₅⟩ => ?_
  -- The header words through `first` and the digits.
  have hw : ∀ {a : Nat}, (a = 216 ∨ a = 248) → word s₅.mem I.B a = word s₃.mem I.B a := fun ha => by
    rw [f₅.word_eq (fun r hr => by
        simp only [dsRanges, hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_using [ha]),
      f₄.word_eq (fun r hr => by
        simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_using [ha])]
  refine ⟨g₅, ?_, ?_, cc, ?_, ccl, fun hX0 => ?_⟩
  · refine (((frm_sq f₁ fun r hr => ?_).trans (frm_sq (Frm.of_outside o₂ (List.mem_singleton_self _)) fun r hr => ?_)).trans
      (frm_sq f₃ fun r hr => ?_)).trans ((frm_sq f₄ fun r hr => ?_).trans (frm_sq f₅ fun r hr => ?_))
    · simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact .inl (by dsimp only; omega_arith)
    · rw [List.mem_singleton.mp hr]; exact .inr (.inl ⟨le_refl _, le_refl _⟩)
    · simp only [nmRanges, hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl
      all_goals first | exact .inl (by dsimp only; omega) | exact .inr (.inr ⟨by dsimp only; omega_using [], by dsimp only; omega_using []⟩)
    · simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl
      all_goals first | exact .inl (by dsimp only; omega) | exact .inr (.inr ⟨by dsimp only; omega, by dsimp only; omega_using []⟩) | exact .inr (.inl ⟨by dsimp only; omega_using [hW], by dsimp only; omega_using []⟩)
    · simp only [dsRanges, hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl | rfl | rfl
      all_goals first | exact .inl (by dsimp only; omega) | exact .inr (.inr ⟨by dsimp only; omega, by dsimp only; omega_using []⟩) | exact .inr (.inl ⟨by dsimp only; omega_using [], by dsimp only; omega_using []⟩)
  · rw [c9, hw (.inr rfl), ← c9, sZ₃]
  · rw [c8, hw (.inl rfl), ← c8, sC₃]
  · -- The first digit at least `2^63`.
    have lo := lo₃ hX0
    have hd : 2 ^ 63 ≤ (word s₄.mem I.B (8 * sS0)).toNat := by
      rw [s0₄]
      refine le_isqrt ?_
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
      calc 2 ^ 63 * 2 ^ 63 * 2 ^ (64 * (Wk I.k - 2)) = 2 ^ (64 * Wk I.k - 2) := by
            rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using [hW]
        _ ≤ _ := lo
    have dv := dv₅ _ hd (v₄ hd) dv₄
    obtain ⟨Sv, R, a1, a2, a3, a4⟩ := dv_last (by omega_using [hW]) dv
    exact ⟨Sv, R, a1, a2, a3, a4⟩

theorem mask_xor_ones (b : Bool) : mask b ^^^ (BitVec.setWidth 64 0#16 - 1#64) = mask (!b) := by cases b <;> rfl

theorem and_mask_zero (x : BitVec 64) (b : Bool) : x &&& mask b = 0 ↔ (x = 0 ∨ b = false) := by
  cases b
  · simp only [show mask false = 0 by decide, or_true, iff_true]; exact BitVec.and_zero
  · simp only [show mask true = BitVec.allOnes 64 by decide, BitVec.and_allOnes, Bool.true_eq_false, or_false]

/-- The tail's head: the bases, `x16` the remainder's, `x9 = 0`, `x14 = W`. -/
theorem stHead_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    WP isa (.block (sqBases ++ [mov .x16 .x10, movi .x9 0, mov .x14 .x12])) s fun t =>
      G I m₀ (Wk I.k) c t ∧ Frm I.B hdrW s.mem t.mem ∧ t.gpr .x16 = off I.B (slot (Wk I.k) wX4) ∧
      t.gpr .x9 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 (Wk I.k) ∧
      Keep [.x3, .x4, .x7, .x9, .x10, .x11, .x12, .x14, .x16] s t := by
  show WP isa (.block (setWid ++ (ws ++ (base wX4 .x10 ++ (base wS .x9 ++ [mov .x11 .x9, movi .x7 0, mov .x16 .x10,
    movi .x9 0, mov .x14 .x12]))))) s _
  rw [WP.block_append_iff]
  refine WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ws_ok g₁.ws.scr g₁.ws.x0 g₁.ws.h256 g₁.ws.hw g₁.ws.hS) fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ => ?_
  have x0₂ : s₂.gpr .x0 = I.B := (k₂.gpr .x0 (by decide)).trans g₁.ws.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok wX4 .x10 x0₂ h11) fun s₃ ⟨⟨h10, m₃, _⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok wS .x9 ((k₃.gpr .x0 (by decide)).trans x0₂) ((k₃.gpr .x11 (by decide)).trans h11))
    fun s₄ ⟨⟨_, m₄, _⟩, k₄⟩ => ?_
  have x12₄ : s₄.gpr .x12 = BitVec.ofNat 64 (Wk I.k) := by rw [k₄.get .x12, k₃.get .x12, h12]
  refine WP.mono (WP.keep [.x7, .x9, .x11, .x14, .x16] (Q := fun t => t.gpr .x16 = s₄.gpr .x10 ∧ t.gpr .x9 = 0 ∧
      t.gpr .x14 = s₄.gpr .x12 ∧ t.mem = s₄.mem) (by brun) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨t16, t9, t14, mt⟩, kt⟩ => ?_
  have m5 : t.mem = s₁.mem := by rw [mt, m₄, m₃, m₂]
  exact ⟨g₁.same m5 (((k₂.trans k₃).trans k₄).trans kt) (by decide), by rw [m5]; exact f₁,
    by rw [t16, k₄.get .x10]; exact h10, t9, by rw [t14, x12₄], ((((k₁.trans k₂).trans k₃).trans k₄).trans kt).mono⟩

/-- What the whole square root writes: also the narrow root `nY`. -/
abbrev sqR2 (k : Nat) : List (Nat × Nat) := sqR (Wk k) ++ [(slot (vk k) nY, 8 * (vk k + 2))]

theorem frm_sq2 {B : Addr} {k : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (f : Frm B rs m m')
    (h : ∀ r ∈ rs, r.1 + r.2 ≤ 256 ∨ (slot (Wk k) wS ≤ r.1 ∧ r.1 + r.2 ≤ slot (Wk k) wS + 8 * (Wk k + 2)) ∨
      (slot (vk k) nY ≤ r.1 ∧ r.1 + r.2 ≤ slot (vk k) nY + 8 * (vk k + 2))) : Frm B (sqR2 k) m m' :=
  f.widen fun r hr => by
    rcases h r hr with h | h | h
    · exact ⟨(0, 256), by simp, Nat.zero_le _, h⟩
    · exact ⟨(slot (Wk k) wS, 8 * (Wk k + 2)), by simp, h.1, h.2⟩
    · exact ⟨(slot (vk k) nY, 8 * (vk k + 2)), by simp, h.1, h.2⟩

/-- The square root's back: the remainder's test into the mask, the root shifted down by `c`, its low `v` words
into `nY`, masked by `X ≠ 0`. -/
theorem sqrtBack_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    {X cc : Nat} (hZ : word s.mem I.B (8 * sZ) = mask (decide (X = 0)))
    (hC : word s.mem I.B (8 * sC) = BitVec.ofNat 64 cc) (hcc : cc ≤ 32 * Wk I.k)
    (hV : X ≠ 0 → ∃ Sv R, wv s.mem I.B (slot (Wk I.k) wS) (Wk I.k) = Sv ∧
      wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = R ∧ R ≤ 2 * Sv ∧ Sv * Sv + R = X * 4 ^ cc) :
    WP isa (seqs (([.block (sqBases ++ [mov .x16 .x10, movi .x9 0, mov .x14 .x12]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16],
      .block ([ldh .x3 sZ, movi .x4 0, .subImm .x .x4 .x4 1, .logic .eor .x .x3 .x3 .x4, .logic .and .x .x9 .x9 .x3] ++
        andZero)] : List (Prog isa)) ++ shiftBy wS true false sC ++
      ([.block setNar, zeroA nY, copyA nY (2 * wS),
       .block (ws ++ base nY .x16 ++ [ldh .x15 sZ, movi .x4 0, .subImm .x .x4 .x4 1, .logic .eor .x .x15 .x15 .x4,
         mov .x14 .x12]),
       countLoop .x14 [ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x16, next .x16]] : List (Prog isa)))) s fun t =>
      G I m₀ (vk I.k) (decide (isqrt X * isqrt X = X) && c) t ∧ Frm I.B (sqR2 I.k) s.mem t.mem ∧
      wv t.mem I.B (slot (vk I.k) nY) (vk I.k) = isqrt X % 2 ^ (64 * vk I.k) := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv : vk I.k < 200 := by simp only [vk]; omega_using [hk2]
  have hv1 : 1 ≤ vk I.k := by simp only [vk]; omega_using []
  have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have qS : slot (Wk I.k) wS = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
  have qY : slot (vk I.k) nY = 256 + 4 * (8 * (vk I.k + 2)) := rfl
  have q10 : slot (vk I.k) (2 * wS) = slot (Wk I.k) wS := by simp only [slot, hdrBytes, wS]; omega_using [hW]
  have cZ : 8 * sZ = 248 := rfl
  have cC : 8 * sC = 216 := rfl
  have cM : 8 * Public.sMask < 256 := by simp only [Public.sMask, sFn]; omega_using []
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) (by simp [shiftBy]) ?_
  simp only [seqs]
  -- The remainder's OR.
  refine WP.seq (WP.mono (stHead_ok h L) fun s₁ ⟨g₁, f₁, x16, x9, x14, k₁⟩ => ?_)
  have hn := g₁.ws.scr.nowrap
  have hZW := g₁.ws.hZ
  have q16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
  refine WP.seq (WP.mono (orAll_ok g₁.ws.scr x16 x14 x9 (by omega_using [hW]) (by omega_using [hW, hv]) (by omega_using [qX, hZW, q16])) fun s₂ ⟨m₂, o9, k₂⟩ => ?_)
  have g₂ : G I m₀ (Wk I.k) c s₂ := g₁.same m₂ k₂ (by decide)
  have z₂ : word s₂.mem I.B (8 * sZ) = mask (decide (X = 0)) := by
    rw [m₂, hdrW_word f₁ (by decide) (by decide) (by decide), hZ]
  -- The mask: `R = 0` where `X ≠ 0`.
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x9] (Q := fun t => t.gpr .x9 = s₂.gpr .x9 &&& mask (!decide (X = 0)) ∧
      t.mem = s₂.mem) (by
    brun [g₂.ws.x0, hdr_enc (show sZ < 32 by decide), g₂.ws.scr.ld (d := 8 * sZ) (by omega_using [cZ, hZW, q16]), z₂, mask_xor_ones])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨x9₃, m₃⟩, k₃⟩ => ?_
  have g₃ : G I m₀ (Wk I.k) c s₃ := g₂.same m₃ k₃ (by decide)
  have hz : s₃.gpr .x9 = 0 ↔ (wv s₁.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = 0 ∨ X = 0) := by
    rw [x9₃, and_mask_zero, o9]; simp
  refine WP.mono (andZero_ok g₃.ws g₃.msk hz) fun s₄ ⟨⟨m₄, _⟩, k₄⟩ => ?_
  have g₄ := g₃.store m₄ k₄ (by decide)
  have o₄ : Outside I.B (8 * Public.sMask) 8 s₃.mem s₄.mem := by
    rw [m₄]; exact writeW_outside s₃.mem I.B _ (by omega_using [cM])
  -- The root shifted down by `c`.
  have c₄ : word s₄.mem I.B (8 * sC) = BitVec.ofNat 64 cc := by
    rw [o₄.word (by simp only [Public.sMask, sFn]; omega_using [cC]) (by omega_using [cC]), m₃, m₂,
      hdrW_word f₁ (by decide) (by decide) (by decide), hC]
  refine WP.mono (shiftBy_ok g₄ L true false (j := wS) (by decide) (sl := sC) (by decide) (by decide) (by decide) c₄
    (N := Wk I.k) rfl (by omega_using [hcc, hW])) fun s₅ ⟨g₅, f₅, v₅, k₅⟩ => ?_
  have S₄ : wv s₄.mem I.B (slot (Wk I.k) wS) (Wk I.k) = wv s.mem I.B (slot (Wk I.k) wS) (Wk I.k) := by
    rw [o₄.wv (by simp only [Public.sMask, sFn]; omega_using [qS]) (by omega_using [hW, hv, qS]), m₃, m₂, Frm.hdrW_wv f₁ (by omega_using [qS]) (by omega_using [hW, hv, qS])]
  rw [S₄] at v₅
  -- The narrow root.
  refine WP.seq (WP.mono (g₅.setNar_ok L) fun s₆ ⟨g₆, f₆, k₆⟩ => ?_)
  refine WP.seq (WP.mono (zeroA_ok g₆.ws (j := nY) (by decide)) fun s₇ ⟨_, o₇, _, _, _, k₇⟩ => ?_)
  have g₇ := g₆.out (by decide) (Nat.le_refl _) o₇ k₇ (by decide)
  refine WP.seq (WP.mono (copyA_ok g₇.ws (o := nY) (a := 2 * wS) (by decide) (by decide) (by decide))
    fun s₈ ⟨v₈, o₈, _, _, k₈⟩ => ?_)
  have g₈ := g₇.out (by decide) (by omega_using []) o₈ k₈ (by decide)
  -- `sZ` through the stores.
  have z₈ : word s₈.mem I.B (8 * sZ) = mask (decide (X = 0)) := by
    rw [o₈.word (by omega_using [qY, cZ]) (by omega_using [cZ]), o₇.word (by omega_using [qY, cZ]) (by omega_using [cZ]), hdrW_word f₆ (by decide) (by decide) (by decide),
      stage_word f₅ (by decide) (by decide) (by decide), o₄.word (by simp only [Public.sMask, sFn]; omega_using [cZ]) (by omega_using [cZ]), m₃,
      z₂]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ws_ok g₈.ws.scr g₈.ws.x0 g₈.ws.h256 g₈.ws.hw g₈.ws.hS) fun s₉ ⟨⟨h12, h11, m₉, _⟩, k₉⟩ => ?_
  refine WP.mono (base_ok nY .x16 ((k₉.gpr .x0 (by decide)).trans g₈.ws.x0) h11) fun s₁₀ ⟨⟨h16, m₁₀, _⟩, k₁₀⟩ => ?_
  have hs₁₀ := g₈.ws.scr.congr (k₉.trans k₁₀).wr
  refine WP.mono (WP.keep [.x4, .x14, .x15] (Q := fun t => t.gpr .x15 = mask (!decide (X = 0)) ∧
      t.gpr .x14 = BitVec.ofNat 64 (vk I.k) ∧ t.mem = s₁₀.mem) (by
    brun [(k₁₀.gpr .x0 (by decide)).trans ((k₉.gpr .x0 (by decide)).trans g₈.ws.x0), hdr_enc (show sZ < 32 by decide),
      hs₁₀.ld (d := 8 * sZ) (by omega_using [cZ, hZW, q16]), m₁₀, m₉, z₈, mask_xor_ones, k₁₀.get .x12, h12])
    (by decide) (by decide) (by decide +kernel)) fun s₁₁ ⟨⟨x15, x14', m₁₁⟩, k₁₁⟩ => ?_
  have m11 : s₁₁.mem = s₈.mem := by rw [m₁₁, m₁₀, m₉]
  have g₁₁ : G I m₀ (vk I.k) _ s₁₁ := g₈.same m11 ((k₉.trans k₁₀).trans k₁₁) (by decide)
  refine WP.mono (maskAll_ok (d := slot (vk I.k) nY) g₁₁.ws.scr (by rw [k₁₁.get .x16]; exact h16) x14' x15 hv1 (by omega_using [hv])
    (by omega_using [hW, qY, hZW, q16]))
    fun t ⟨vt, ot, kt⟩ => ?_
  have gt := g₁₁.out (by decide) (by omega_using []) ot kt (by decide)
  -- The mask.
  have R₁ : wv s₁.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) :=
    Frm.hdrW_wv f₁ (by omega_using [qX]) (by omega_using [hW, hv, qX])
  have hdec : decide (wv s₁.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = 0 ∨ X = 0) = decide (isqrt X * isqrt X = X) := by
    by_cases hX : X = 0
    · subst hX; simp [isqrt_zero]
    · obtain ⟨Sv, R, a1, a2, a3, a4⟩ := hV hX
      have := (sqrt_vals a4 a3).2
      rw [R₁, a2]
      exact decide_eq_decide.mpr (by simp only [hX, or_false]; exact this)
  rw [hdec] at gt
  refine ⟨gt, ?_, ?_⟩
  · refine (frm_sq2 f₁ fun r hr => ?_).trans ((by rw [m₃, m₂]; exact Frm.refl _ _ _ : Frm I.B (sqR2 I.k) s₁.mem s₃.mem).trans
      ((frm_sq2 (Frm.of_outside o₄ (List.mem_singleton_self _)) fun r hr => ?_).trans
      ((frm_sq2 f₅ fun r hr => ?_).trans ((frm_sq2 f₆ fun r hr => ?_).trans
      ((frm_sq2 (Frm.of_outside o₇ (List.mem_singleton_self _)) fun r hr => ?_).trans
      ((frm_sq2 (Frm.of_outside o₈ (List.mem_singleton_self _)) fun r hr => ?_).trans
      ((by rw [m11]; exact Frm.refl _ _ _ : Frm I.B (sqR2 I.k) s₈.mem s₁₁.mem).trans
      (frm_sq2 (Frm.of_outside ot (List.mem_singleton_self _)) fun r hr => ?_))))))))
    all_goals first
      | (simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl <;> exact .inl (by dsimp only; simp only [sW, sArr, sStride, sFn]; omega_using []))
      | (simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with (rfl | rfl | rfl) | rfl
         all_goals first | exact .inl (by dsimp only; simp only [sW, sArr, sStride, sFn]; omega_using []) |
           exact .inr (.inl ⟨by dsimp only; omega, by dsimp only; omega_using []⟩))
      | (rw [List.mem_singleton.mp hr]
         first | exact .inl (by dsimp only; omega) | exact .inr (.inr ⟨by dsimp only; omega_using [], by dsimp only; omega_using []⟩))
  · -- The root.
    have Y : wv s₁₁.mem I.B (slot (vk I.k) nY) (vk I.k) =
        wv s.mem I.B (slot (Wk I.k) wS) (Wk I.k) / 2 ^ cc % 2 ^ (64 * vk I.k) := by
      rw [m11, v₈, o₇.wv (by omega_using [hW, qS, qY, q10]) (by omega_using [hW, hv, qS, q10]), Frm.hdrW_wv f₆ (by omega_using [qS, q10]) (by omega_using [hW, hv, qS, q10]), q10,
        ← wv_mod_low' s₅.mem I.B _ (vk I.k) (vk I.k + 2), show vk I.k + (vk I.k + 2) = Wk I.k by omega_using [hW], v₅]
      rfl
    rw [vt, Y]
    by_cases hX : X = 0
    · subst hX; simp [isqrt_zero]
    · obtain ⟨Sv, R, a1, a2, a3, a4⟩ := hV hX
      rw [a1, (sqrt_vals a4 a3).1]
      simp [hX]

/-- `sqrt`: of `X` (wide array `wX4`), `⌊√X⌋ mod 2^(64 v)` into narrow `nY`, `⌊√X⌋² = X` and'ed into the mask, and
narrow arrays 0, 1 and 6 to 9 kept. -/
theorem sqrt_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) {X : Nat}
    (hX : wv s.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = X) :
    WP isa sqrt s fun t =>
      G I m₀ (vk I.k) (decide (isqrt X * isqrt X = X) && c) t ∧
      wv t.mem I.B (slot (vk I.k) nY) (vk I.k) = isqrt X % 2 ^ (64 * vk I.k) ∧
      (∀ j k, (j = 0 ∨ j = 1 ∨ (6 ≤ j ∧ j < 10)) → k ≤ vk I.k + 2 →
        wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  unfold sqrt
  rw [show ∀ (a b c d e f g h : Prog isa) (S T : List (Prog isa)),
    [a, b, c, d, e, f, g, h] ++ S ++ T = [a, b, c, d, e] ++ ([f, g, h] ++ S ++ T) from fun _ _ _ _ _ _ _ _ _ _ => rfl]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (sqrtFront_ok h L) fun u ⟨gu, fu, zu, cc, cu, ccl, vu⟩ => ?_)
  rw [hX] at zu vu
  refine WP.mono (sqrtBack_ok gu L zu cu ccl vu) fun t ⟨gt, ft, vt⟩ => ⟨gt, vt, fun j k hj hk => ?_⟩
  have F : Frm I.B (sqR2 I.k) s.mem t.mem := (fu.mono fun r hr => List.mem_append_left _ hr).trans ft
  have q16 : slot (Wk I.k) 16 = 256 + 16 * (8 * (Wk I.k + 2)) := rfl
  have qX : slot (Wk I.k) wX4 = 256 + 7 * (8 * (Wk I.k + 2)) := rfl
  have qS : slot (Wk I.k) wS = 256 + 5 * (8 * (Wk I.k + 2)) := rfl
  have qY : slot (vk I.k) nY = 256 + 4 * (8 * (vk I.k + 2)) := rfl
  have hj' : j = 0 ∨ j = 1 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega_using [hj]
  have hZv := gt.ws.hZ
  have qv16 : slot (vk I.k) 16 = 256 + 16 * (8 * (vk I.k + 2)) := rfl
  have qj : ∀ i, slot (vk I.k) i = 256 + i * (8 * (vk I.k + 2)) := fun _ => rfl
  rw [qj]
  refine F.wv_eq (fun r hr => ?_) (by rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  simp only [sqR2, sqR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl <;> dsimp only <;> rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> omega_arith

end VG.Proof.Rsa.AArch64.Rd
