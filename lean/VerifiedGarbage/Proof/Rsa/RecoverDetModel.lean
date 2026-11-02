module
public import VerifiedGarbage.Proof.Rsa.RecoverDet

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

/-!
# Appendix C.2 with fixed steps and masks: the model

What code with `nb`-bit narrow and `wb`-bit wide numbers computes for
Appendix C.2 (`Spec.Rsa.recoverDet`), every operation modulo its width and
every check a flag, as a function of `n` and the product `d e`:

* `d e - 1` (`deX`) and whether `d e ≥ 2` (`okDE`);
* the halvings (`twoStep`) from `(n - 1, x, x)`, `x` its narrow part;
* `a`, the product of the GCD and the doubled `x` (`prodStep`), and `m`, `r`;
* `m + 1` and `n - r`, whose quotient and remainder (`q`, `rem`), as a
  division by zero leaves them unknown, are the second stage's inputs
  (`stage2`): `b`, `b²` (`prodStep`), `b² - 4 n` and its square root
  (`sqrtStep`), and the factors.

`model_correct`: with the quotient and remainder of the division where the
divisor is positive, the mask and the factors are `recoverDet`'s result.
-/

@[expose] public section

namespace VG.Proof.Rsa.RecoverDet

open VG.Spec.Rsa (isqrt recoverDet)

/-- `a - c` modulo `2^b`, for `a, c < 2^b`. -/
def wsub (b a c : Nat) : Nat := (a + 2 ^ b - c) % 2 ^ b

def deX (wb de : Nat) : Nat := wsub wb de 1

def okDE (wb de : Nat) : Bool := !(decide (de < 1) || decide (deX wb de < 1))

def twosOut (nb wb n de : Nat) : Nat × Nat × Nat :=
  (twoStep wb)^[nb] (wsub nb n 1, deX wb de % 2 ^ nb, deX wb de)

def aOf (nb wb n de : Nat) : Nat :=
  ((prodStep wb)^[nb] (Nat.gcd (twosOut nb wb n de).1 (twosOut nb wb n de).2.1,
    (twosOut nb wb n de).2.2, 0)).2.2

def mOf (nb wb n de : Nat) : Nat := aOf nb wb n de / n
def rOf (nb wb n de : Nat) : Nat := aOf nb wb n de % n

def ltOf (nb wb n de : Nat) : Bool := decide (mOf nb wb n de < n)

/-- `m + 1`, narrow, and `n - r`. -/
def m1Of (nb wb n de : Nat) : Nat := (mOf nb wb n de % 2 ^ nb + 1) % 2 ^ nb
def dOf (nb wb n de : Nat) : Nat := wsub nb n (rOf nb wb n de % 2 ^ nb)

/-- `b`, from the quotient. -/
def bOf (nb q : Nat) : Nat := (q + 1) % 2 ^ nb

/-- `b² - 4 n` modulo `2^wb`, from `b² = (prodStep …).2.2`. -/
def sqOf (nb wb b : Nat) : Nat := ((prodStep wb)^[nb] (b, b, 0)).2.2
def fourN (wb n : Nat) : Nat := 2 * (2 * n % 2 ^ wb) % 2 ^ wb
def xOf (nb wb n b : Nat) : Nat := wsub wb (sqOf nb wb b) (fourN wb n)

def ok4Of (nb wb n b : Nat) : Bool :=
  !(decide (sqOf nb wb b < fourN wb n) || decide (xOf nb wb n b < 1))

def rootOf (nb wb n b : Nat) : Nat × Nat × Nat := (sqrtStep nb wb)^[wb / 2] (xOf nb wb n b, 0, 0)

/-- The mask and the factors, given the quotient and remainder of `n - r` by `m + 1`. -/
def stage2 (nb wb n q rem : Nat) : Bool × Nat × Nat :=
  let b := bOf nb q
  let y := (rootOf nb wb n b).2.2
  (decide (rem = 0) && ok4Of nb wb n b && decide ((rootOf nb wb n b).2.1 = 0),
    (b + y) % 2 ^ nb / 2, wsub nb b y / 2)

def result (nb wb n de q rem : Nat) : Option (Nat × Nat) :=
  if okDE wb de && ltOf nb wb n de && (stage2 nb wb n q rem).1 then
    some ((stage2 nb wb n q rem).2.1, (stage2 nb wb n q rem).2.2)
  else none

theorem wsub_of_le {b a c : Nat} (ha : a < 2 ^ b) (hc : c ≤ a) : wsub b a c = a - c := by
  unfold wsub
  rw [show a + 2 ^ b - c = (a - c) + 2 ^ b by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem wsub_of_lt {b a c : Nat} (hc : c < 2 ^ b) (h : a < c) : wsub b a c = a + 2 ^ b - c := by
  unfold wsub
  rw [Nat.mod_eq_of_lt (by omega)]

/-! ## The steps as code computes them, with carries -/

/-- An addition by two subtractions: `a - (0 - c) = a + c`. -/
theorem wsub_neg {b a c : Nat} (ha : a < 2 ^ b) (hc : c < 2 ^ b) : wsub b a (wsub b 0 c) = (a + c) % 2 ^ b := by
  unfold wsub
  rcases Nat.eq_zero_or_pos c with rfl | pos
  · simp [Nat.mod_eq_of_lt ha]
  · rw [show 0 + 2 ^ b - c = 2 ^ b - c by omega, Nat.mod_eq_of_lt (show 2 ^ b - c < 2 ^ b by omega),
      show a + 2 ^ b - (2 ^ b - c) = a + c by omega]

/-- A doubling modulo `2^b` and a bit shifted in. -/
theorem dbl_add {b a c : Nat} (hb : 1 ≤ b) (hc : c ≤ 1) : 2 * a % 2 ^ b + c = (2 * a + c) % 2 ^ b := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
  have hk := Nat.two_pow_pos k
  generalize 2 ^ k = Q at hk ⊢
  have := Nat.mod_lt a hk
  have e2 : 2 * a + c = (2 * (a % Q) + c) + (2 * Q) * (a / Q) :=
    calc 2 * a + c = 2 * (a % Q + Q * (a / Q)) + c := by rw [Nat.mod_add_div]
      _ = (2 * (a % Q) + c) + (2 * Q) * (a / Q) := by rw [Nat.mul_add, Nat.mul_assoc]; omega
  rw [Nat.mul_mod_mul_left]
  conv_rhs => rw [e2, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The bit a doubling shifts out. -/
theorem two_div_le {x P : Nat} (h : x < P) : 2 * x / P ≤ 1 :=
  Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by omega))

/-- A step of the square root as code computes it: the radicand doubled twice, its bits shifted
into the remainder, and `4 y + 1` compared with the remainder. -/
theorem sqrtStep_code {nb wb X R Y : Nat} (hnb : 1 ≤ nb) (hX : X < 2 ^ wb) :
    sqrtStep nb wb (X, R, Y) =
      (2 * (2 * X % 2 ^ wb) % 2 ^ wb,
        if (2 * ((2 * R + 2 * X / 2 ^ wb) % 2 ^ nb) + 2 * (2 * X % 2 ^ wb) / 2 ^ wb) % 2 ^ nb <
            (2 * (2 * Y % 2 ^ nb) + 1) % 2 ^ nb
        then (2 * ((2 * R + 2 * X / 2 ^ wb) % 2 ^ nb) + 2 * (2 * X % 2 ^ wb) / 2 ^ wb) % 2 ^ nb
        else wsub nb ((2 * ((2 * R + 2 * X / 2 ^ wb) % 2 ^ nb) + 2 * (2 * X % 2 ^ wb) / 2 ^ wb) % 2 ^ nb)
          ((2 * (2 * Y % 2 ^ nb) + 1) % 2 ^ nb),
        (2 * Y + if (2 * ((2 * R + 2 * X / 2 ^ wb) % 2 ^ nb) + 2 * (2 * X % 2 ^ wb) / 2 ^ wb) % 2 ^ nb <
            (2 * (2 * Y % 2 ^ nb) + 1) % 2 ^ nb then 0 else 1) % 2 ^ nb) := by
  have hi := two_div_le hX
  have lo := two_div_le (Nat.mod_lt (2 * X) (Nat.two_pow_pos wb))
  unfold sqrtStep
  simp only
  rw [dbl_add hnb hi, dbl_add hnb lo, dbl_add hnb (show 1 ≤ 1 by omega)]
  have hr := Nat.mod_lt (2 * ((2 * R + 2 * X / 2 ^ wb) % 2 ^ nb) + 2 * (2 * X % 2 ^ wb) / 2 ^ wb)
    (Nat.two_pow_pos nb)
  generalize (2 * ((2 * R + 2 * X / 2 ^ wb) % 2 ^ nb) + 2 * (2 * X % 2 ^ wb) / 2 ^ wb) % 2 ^ nb = r at hr ⊢
  generalize (2 * (2 * Y % 2 ^ nb) + 1) % 2 ^ nb = t
  split
  · simp
  · rename_i c
    simp only [Prod.mk.injEq, true_and]
    refine ⟨(wsub_of_le hr (by omega)).symm, by rw [Nat.add_zero, dbl_add hnb (show 1 ≤ 1 by omega)]⟩

/-- With the division's quotient and remainder where its divisor is positive, the mask and
factors are Appendix C.2's result. -/
theorem model_correct {nb wb n e d q rem : Nat} (odd : n % 2 = 1) (three : 3 ≤ n)
    (hn : 8 * (n + 2) ≤ 2 ^ nb) (hde : d * e < 2 ^ nb) (hw : 2 * nb ≤ wb) (hwe : wb % 2 = 0)
    (hdiv : 0 < m1Of nb wb n (d * e) →
      q = dOf nb wb n (d * e) / m1Of nb wb n (d * e) ∧ rem = dOf nb wb n (d * e) % m1Of nb wb n (d * e)) :
    result nb wb n (d * e) q rem = recoverDet n e d := by
  have pnb : 2 ^ nb ≤ 2 ^ wb := Nat.pow_le_pow_right (by decide) (by omega)
  have p2 : 2 ^ nb * 2 ^ nb ≤ 2 ^ wb := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have p64 : 1 ≤ 2 ^ nb := Nat.one_le_two_pow
  generalize hde' : d * e = de at *
  unfold result recoverDet
  rw [hde']
  by_cases small : de < 2
  · -- `d e < 2`: the first check fails.
    have : okDE wb de = false := by
      unfold okDE deX
      rcases (show de = 0 ∨ de = 1 by omega) with rfl | rfl
      · simp
      · simp [wsub]
    simp [this, small]
  have ok1 : okDE wb de = true := by
    unfold okDE deX
    rw [wsub_of_le (by omega) (by omega)]
    simp; omega
  simp only [ok1, small, ↓reduceIte, Bool.true_and]
  -- The halvings and the GCD.
  have dx : deX wb de = de - 1 := wsub_of_le (by omega) (by omega)
  have xlt : de - 1 < 2 ^ nb := by omega
  have un : wsub nb n 1 = n - 1 := wsub_of_le (by omega) (by omega)
  obtain ⟨uodd, ule, g, hx2, hx3, hgcd⟩ :=
    twos_iter (b := wb) (N := n - 1) (x := de - 1) (k := nb) (by omega) (by omega) (by omega)
  have tw : twosOut nb wb n de = (twoStep wb)^[nb] (n - 1, de - 1, de - 1) := by
    unfold twosOut; rw [un, dx, Nat.mod_eq_of_lt xlt]
  generalize (twoStep wb)^[nb] (n - 1, de - 1, de - 1) = s at tw uodd ule hx2 hx3 hgcd
  obtain ⟨u, x2, x3⟩ := s
  simp only at uodd ule hx2 hx3 hgcd
  have gpos : 0 < Nat.gcd (n - 1) (de - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have gle : Nat.gcd (n - 1) (de - 1) ≤ n - 1 := Nat.gcd_le_left _ (by omega)
  have g_le : g ≤ Nat.gcd (n - 1) (de - 1) := by
    rw [hgcd]; exact Nat.le_mul_of_pos_right _ (Nat.gcd_pos_of_pos_left _ (by omega))
  have big : (de - 1) * Nat.gcd (n - 1) (de - 1) < 2 ^ wb := by
    calc (de - 1) * Nat.gcd (n - 1) (de - 1) < 2 ^ nb * 2 ^ nb :=
          Nat.mul_lt_mul'' xlt (by omega)
      _ ≤ 2 ^ wb := p2
  have x3v : x3 = (de - 1) * g := by
    rw [hx3]; exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left _ g_le) big)
  have g1le : Nat.gcd u x2 ≤ n - 1 := le_trans (Nat.gcd_le_left _ (by omega)) ule
  have ha : aOf nb wb n de = (de - 1) * Nat.gcd (n - 1) (de - 1) := by
    unfold aOf
    rw [tw, prod_iter _ _ _ (by rw [x3v]; exact lt_of_le_of_lt (Nat.mul_le_mul_left _ g_le) big)]
    simp only
    rw [Nat.mod_eq_of_lt (show Nat.gcd u x2 < 2 ^ nb by omega), x3v, hgcd]
    rw [Nat.mod_eq_of_lt (by rw [hgcd] at big; ring_nf at big ⊢; exact big)]
    ring
  generalize hA : (de - 1) * Nat.gcd (n - 1) (de - 1) = a at *
  have hm : mOf nb wb n de = a / n := by rw [mOf, ha]
  have hr : rOf nb wb n de = a % n := by rw [rOf, ha]
  have rlt : a % n < n := Nat.mod_lt _ (by omega)
  -- `m ≥ n`: the division's check fails.
  by_cases lt : a / n < n
  swap
  · have : ltOf nb wb n de = false := by simp [ltOf, hm, lt]
    simp only [this, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have : (n - a % n) % (a / n + 1) ≠ 0 := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [this]
  have : ltOf nb wb n de = true := by simp [ltOf, hm, lt]
  simp only [this, Bool.true_and]
  have m1 : m1Of nb wb n de = a / n + 1 := by
    unfold m1Of; rw [hm, Nat.mod_eq_of_lt (a := a / n) (by omega), Nat.mod_eq_of_lt (by omega)]
  have dv : dOf nb wb n de = n - a % n := by
    unfold dOf; rw [hr, Nat.mod_eq_of_lt (by omega), wsub_of_le (by omega) (by omega)]
  obtain ⟨hq, hrem⟩ := hdiv (by omega)
  rw [m1, dv] at hq hrem
  subst hq hrem
  unfold stage2
  simp only
  by_cases exact : (n - a % n) % (a / n + 1) = 0
  swap
  · simp [exact]
  simp only [exact, decide_true, Bool.true_and, ne_eq, not_true_eq_false, ↓reduceIte]
  -- `b`.
  have qle : (n - a % n) / (a / n + 1) ≤ n := le_trans (Nat.div_le_self _ _) (by omega)
  have hb : bOf nb ((n - a % n) / (a / n + 1)) = (n - a % n) / (a / n + 1) + 1 := by
    unfold bOf; exact Nat.mod_eq_of_lt (by omega)
  rw [hb]
  have blt : (n - a % n) / (a / n + 1) + 1 < 2 ^ nb := by omega
  have bn : (n - a % n) / (a / n + 1) + 1 ≤ n + 1 := by omega
  generalize (n - a % n) / (a / n + 1) + 1 = b at *
  have bb : b * b < 2 ^ wb := lt_of_lt_of_le (Nat.mul_lt_mul'' blt blt) p2
  have sq : sqOf nb wb b = b * b := by
    unfold sqOf; rw [prod_iter _ _ _ (by omega)]; simp only
    rw [Nat.mod_eq_of_lt blt, Nat.mod_eq_of_lt bb]
  have f4 : fourN wb n = 4 * n := by
    unfold fourN
    rw [Nat.mod_eq_of_lt (a := 2 * n) (by omega), Nat.mod_eq_of_lt (by omega)]; ring
  -- `b² ≤ 4 n`: the third check fails.
  by_cases le4 : b * b ≤ 4 * n
  · have : ok4Of nb wb n b = false := by
      unfold ok4Of xOf
      rw [sq, f4]
      rcases Nat.lt_or_eq_of_le le4 with c | c
      · simp [c]
      · rw [c, wsub_of_le (by omega) (le_refl _)]; simp
    simp [this, le4]
  have xv : xOf nb wb n b = b * b - 4 * n := by
    unfold xOf; rw [sq, f4, wsub_of_le bb (by omega)]
  have : ok4Of nb wb n b = true := by
    unfold ok4Of; rw [xv, sq, f4]; simp; omega
  simp only [this, le4, Bool.true_and, ↓reduceIte]
  -- The square root.
  have rootLt : isqrt (b * b - 4 * n) < b := by
    by_contra c
    have := isqrt_sq_le (b * b - 4 * n)
    have : b * b ≤ isqrt (b * b - 4 * n) * isqrt (b * b - 4 * n) := Nat.mul_self_le_mul_self (by omega)
    omega
  have K : 4 ^ (wb / 2) = 2 ^ wb := by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]; congr 1; omega
  obtain ⟨ry, rr⟩ := sqrt_iter (nb := nb) (K := wb / 2) (X := b * b - 4 * n) (by rw [K]; omega)
    (by have := Nat.div_mul_le_self (2 ^ nb) 8; have : n + 1 < 2 ^ nb / 8 := by omega
        omega)
  have wbK : 2 * (wb / 2) = wb := by omega
  rw [wbK] at ry rr
  unfold rootOf
  rw [xv, ry]
  generalize isqrt (b * b - 4 * n) = γ at *
  generalize ((sqrtStep nb wb)^[wb / 2] (b * b - 4 * n, 0, 0)).2.1 = rm at *
  by_cases ex : γ * γ = b * b - 4 * n
  · have : rm = 0 := by omega
    simp only [this, decide_true, ex, not_true_eq_false, ↓reduceIte, Option.some.injEq,
      Prod.mk.injEq]
    exact ⟨by rw [Nat.mod_eq_of_lt (by omega)], by rw [wsub_of_le blt (by omega)]⟩
  · have : rm ≠ 0 := by omega
    simp [this, ex]

end VG.Proof.Rsa.RecoverDet

namespace VG.Proof.Rsa.RecoverDet

open VG.Spec.Rsa (isqrt recoverDet)

/-- Appendix C.2's factors multiply to the modulus: `p q = (b² - ϒ²) / 4 = n`. -/
theorem recoverDet_mul {n e d p q : Nat} (h : recoverDet n e d = some (p, q)) : p * q = n := by
  unfold recoverDet at h
  simp only at h
  split at h
  · cases h
  split at h
  · cases h
  generalize (n - (d * e - 1) * Nat.gcd (n - 1) (d * e - 1) % n) /
    ((d * e - 1) * Nat.gcd (n - 1) (d * e - 1) / n + 1) + 1 = b at h
  split at h
  · cases h
  rename_i big
  generalize isqrt (b * b - 4 * n) = γ at h
  split at h
  · cases h
  rename_i ex
  simp only [ne_eq, Decidable.not_not] at ex
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have gb : γ ≤ b := by
    by_contra c
    have : b * b < γ * γ := Nat.mul_self_lt_mul_self (by omega)
    omega
  obtain ⟨δ, rfl⟩ : ∃ δ, b = γ + δ := ⟨b - γ, by omega⟩
  have e1 : (γ + δ) * (γ + δ) - 4 * n = γ * γ + δ * (δ + 2 * γ) - 4 * n := by
    congr 1; ring
  rw [e1] at ex
  have prod : δ * (δ + 2 * γ) = 4 * n := by omega
  obtain ⟨k, rfl⟩ : ∃ k, δ = 2 * k := by
    refine ⟨δ / 2, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one δ with h0 | h1
    · omega
    · exfalso
      have : (δ * (δ + 2 * γ)) % 2 = 1 := by
        rw [Nat.mul_mod, h1, Nat.add_mod, h1]; simp
      omega
  have e2 : (γ + 2 * k + γ) / 2 = γ + k := by omega
  have e3 : (γ + 2 * k - γ) / 2 = k := by omega
  rw [e2, e3]
  have : 2 * k * (2 * k + 2 * γ) = 4 * ((γ + k) * k) := by ring
  omega

end VG.Proof.Rsa.RecoverDet
