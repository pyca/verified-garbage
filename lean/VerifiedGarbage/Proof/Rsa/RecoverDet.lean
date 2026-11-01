module
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import Mathlib.Logic.Function.Iterate

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# Prime recovery by SP 800-56B Rev. 2 Appendix C.2: the mathematics

Target-independent models, on naturals, of the fixed-step loops that compute
Appendix C.2 (`Spec.Rsa.recoverDet`) without a branch on a secret:

* `Spec.Rsa.isqrt` is the greatest `s` with `s² ≤ x` (`isqrt_sq_le`,
  `lt_succ_isqrt_sq`, `isqrt_eq`).
* One step of the square root two bits at a time (`sqrt_step`): from
  `y = isqrt t` and `r = t - y²`, the next two bits `δ` give
  `isqrt (4 t + δ)` and its remainder by one comparison of `4 r + δ` with
  `4 y + 1`.
* Halvings of `u` while it is even, and of `x` while both are even, doubling
  `x' = 2^k x` (`twoStep`): from `u = n - 1`, as many as `n - 1` has bits
  leave `u` odd and `gcd(n - 1, x) = 2^k gcd(u, x / 2^k)` (`twos_iter`).
* A product by the bits of the multiplier, from the bottom, each doubling
  the multiplicand (`prodStep`), modulo `2^b` (`prod_iter`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RecoverDet

open VG.Spec.Rsa (isqrt)

/-! ## The integer square root -/

theorem isqrt_spec (x : Nat) : isqrt x * isqrt x ≤ x ∧ x < (isqrt x + 1) * (isqrt x + 1) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [isqrt]
    split
    · rename_i h
      constructor
      · interval_cases x <;> decide
      · interval_cases x <;> decide
    · rename_i h
      have h4 : x / 4 < x := by omega
      obtain ⟨lo, hi⟩ := ih (x / 4) h4
      dsimp only
      generalize isqrt (x / 4) = s at lo hi
      have q := Nat.div_add_mod x 4
      have r := Nat.mod_lt x (show 0 < 4 by decide)
      have e1 : 2 * s * (2 * s) = 4 * (s * s) := by ring
      have e2 : (2 * s + 1) * (2 * s + 1) = 4 * (s * s) + 4 * s + 1 := by ring
      have e3 : (2 * s + 1 + 1) * (2 * s + 1 + 1) = 4 * ((s + 1) * (s + 1)) := by ring
      have e4 : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by ring
      split
      · rename_i c
        refine ⟨c, ?_⟩
        omega
      · rename_i c
        refine ⟨by omega, by omega⟩

theorem isqrt_zero : isqrt 0 = 0 := by rw [isqrt]; simp

theorem isqrt_sq_le (x : Nat) : isqrt x * isqrt x ≤ x := (isqrt_spec x).1

theorem lt_succ_isqrt_sq (x : Nat) : x < (isqrt x + 1) * (isqrt x + 1) := (isqrt_spec x).2

/-- The integer square root is the `s` with `s² ≤ x < (s + 1)²`. -/
theorem isqrt_eq {x s : Nat} (lo : s * s ≤ x) (hi : x < (s + 1) * (s + 1)) : isqrt x = s := by
  obtain ⟨l, h⟩ := isqrt_spec x
  rcases Nat.lt_trichotomy (isqrt x) s with c | c | c
  · have : (isqrt x + 1) * (isqrt x + 1) ≤ s * s := Nat.mul_self_le_mul_self (by omega)
    omega
  · exact c
  · have : (s + 1) * (s + 1) ≤ isqrt x * isqrt x := Nat.mul_self_le_mul_self (by omega)
    omega

/-- One step of the square root: from the root `y` of `t` and its remainder `r`, the root of
`4 t + δ` is `2 y + 1` if `4 y + 1 ≤ 4 r + δ`, else `2 y`. -/
theorem sqrt_step {t y r δ : Nat} (hy : y = isqrt t) (hr : r + y * y = t) (hδ : δ < 4) :
    isqrt (4 * t + δ) = (if 4 * y + 1 ≤ 4 * r + δ then 2 * y + 1 else 2 * y) ∧
      (if 4 * y + 1 ≤ 4 * r + δ then 4 * r + δ - (4 * y + 1) else 4 * r + δ) +
        isqrt (4 * t + δ) * isqrt (4 * t + δ) = 4 * t + δ ∧
      (if 4 * y + 1 ≤ 4 * r + δ then 4 * r + δ - (4 * y + 1) else 4 * r + δ) ≤
        2 * isqrt (4 * t + δ) := by
  have hi := lt_succ_isqrt_sq t
  rw [← hy] at hi
  have e1 : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by ring
  have hr2 : r ≤ 2 * y := by omega
  have e2 : (2 * y + 1) * (2 * y + 1) = 4 * (y * y) + 4 * y + 1 := by ring
  have e3 : (2 * y + 1 + 1) * (2 * y + 1 + 1) = 4 * (y * y) + 8 * y + 4 := by ring
  have e4 : 2 * y * (2 * y) = 4 * (y * y) := by ring
  have e5 : (2 * y + 1) * (2 * y + 1) = 4 * (y * y) + 4 * y + 1 := by ring
  split
  · rename_i c
    have e : isqrt (4 * t + δ) = 2 * y + 1 := isqrt_eq (by omega) (by omega)
    refine ⟨e, ?_, ?_⟩ <;> rw [e] <;> omega
  · rename_i c
    have e : isqrt (4 * t + δ) = 2 * y := isqrt_eq (by omega) (by omega)
    refine ⟨e, ?_, ?_⟩ <;> rw [e] <;> omega

/-! ## The halvings -/

/-- A step of the halvings: `u` halved if even, and `x` halved and `x'` doubled (modulo `2^b`)
if both are. -/
def twoStep (b : Nat) (s : Nat × Nat × Nat) : Nat × Nat × Nat :=
  if s.1 % 2 = 0 then
    if s.2.1 % 2 = 0 then (s.1 / 2, s.2.1 / 2, 2 * s.2.2 % 2 ^ b) else (s.1 / 2, s.2.1, s.2.2)
  else s

/-- What the halvings keep after `i` steps from `(n - 1, x, x)`. -/
def TwoInv (b N x i : Nat) (s : Nat × Nat × Nat) : Prop :=
  ∃ g e, s.2.1 * g = x ∧ s.2.2 = x * g % 2 ^ b ∧
    Nat.gcd N x = g * Nat.gcd (s.1 * 2 ^ e) s.2.1 ∧ (e = 0 ∨ s.2.1 % 2 = 1) ∧
    (s.1 % 2 = 1 ∨ s.1 * 2 ^ i = N) ∧ s.1 ≤ N

theorem twoInv_step {b N x i : Nat} {s : Nat × Nat × Nat} (h : TwoInv b N x i s) :
    TwoInv b N x (i + 1) (twoStep b s) := by
  obtain ⟨u, x2, x3⟩ := s
  obtain ⟨g, e, hx, h3, hg, he, hu, hle⟩ := h
  simp only at hx h3 hg he hu hle
  unfold twoStep
  simp only
  by_cases eu : u % 2 = 0
  · simp only [eu, ↓reduceIte]
    have hu' : u / 2 % 2 = 1 ∨ u / 2 * 2 ^ (i + 1) = N := by
      rcases hu with hu | hu
      · omega
      · right; rw [← hu, Nat.pow_succ]; have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero eu); grind
    by_cases ex : x2 % 2 = 0
    · simp only [ex, ↓reduceIte]
      have e0 : e = 0 := by omega
      subst e0
      refine ⟨2 * g, 0, ?_, ?_, ?_, .inl rfl, hu', by simp only; omega⟩
      · simp only; rw [← hx]; have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ex); grind
      · simp only; rw [h3, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]; grind
      · simp only [Nat.pow_zero, Nat.mul_one] at hg ⊢
        rw [hg]
        have du := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero eu)
        have dx := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ex)
        conv_lhs => rw [← du, ← dx]
        rw [Nat.gcd_mul_right]
        ring
    · simp only [ex, ↓reduceIte]
      refine ⟨g, e + 1, hx, h3, ?_, .inr (by simp only; omega), hu', by simp only; omega⟩
      simp only
      rw [hg]
      have du := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero eu)
      congr 2
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (u / 2 * 2 ^ e) 2, ← Nat.mul_assoc,
        Nat.mul_comm 2 (u / 2), du]
  · simp only [eu, ↓reduceIte]
    exact ⟨g, e, hx, h3, hg, he, .inl (by omega), hle⟩

theorem twoInv_iter {b N x : Nat} : ∀ k i (s : Nat × Nat × Nat), TwoInv b N x i s →
    TwoInv b N x (i + k) ((twoStep b)^[k] s)
  | 0, _, _, h => h
  | k + 1, i, s, h => by
    rw [Function.iterate_succ_apply, show i + (k + 1) = (i + 1) + k by omega]
    exact twoInv_iter k (i + 1) _ (twoInv_step h)

/-- After as many steps as `N` has bits, from `(N, x, x)`: `u` is odd, and
`gcd(N, x) = 2^k gcd(u, x / 2^k)` with `x' = 2^k x` (modulo `2^b`). -/
theorem twos_iter {b N x k : Nat} (pos : 0 < N) (hk : N < 2 ^ k) (hx : x < 2 ^ b) :
    ((twoStep b)^[k] (N, x, x)).1 % 2 = 1 ∧ ((twoStep b)^[k] (N, x, x)).1 ≤ N ∧ ∃ g, ((twoStep b)^[k] (N, x, x)).2.1 * g = x ∧
      ((twoStep b)^[k] (N, x, x)).2.2 = x * g % 2 ^ b ∧
      Nat.gcd N x = g * Nat.gcd ((twoStep b)^[k] (N, x, x)).1 ((twoStep b)^[k] (N, x, x)).2.1 := by
  have start : TwoInv b N x 0 (N, x, x) :=
    ⟨1, 0, Nat.mul_one _, by simp only [Nat.mul_one]; exact (Nat.mod_eq_of_lt hx).symm,
      by simp, .inl rfl, .inr (by simp), le_refl _⟩
  obtain ⟨g, e, hx, h3, hg, he, hu, hle⟩ := twoInv_iter k 0 _ start
  generalize (twoStep b)^[k] (N, x, x) = s at *
  obtain ⟨u, x2, x3⟩ := s
  simp only [Nat.zero_add] at hx h3 hg he hu hle ⊢
  have odd : u % 2 = 1 := by
    rcases hu with hu | hu
    · exact hu
    · exfalso
      rcases Nat.eq_zero_or_pos u with z | p
      · rw [z, Nat.zero_mul] at hu; omega
      · have := Nat.mul_le_mul_right (2 ^ k) (show 1 ≤ u from p)
        omega
  refine ⟨odd, hle, g, hx, h3, ?_⟩
  rw [hg]
  rcases he with rfl | he
  · rw [Nat.pow_zero, Nat.mul_one]
  · congr 1
    exact Nat.Coprime.gcd_mul_right_cancel _ (Nat.Coprime.pow_left _ (by
      unfold Nat.Coprime; rw [Nat.gcd_rec, he]; rfl))

/-! ## Products -/

/-- A step of the product: the multiplier `y` halved, the multiplicand `x` doubled and the
accumulator `a` plus `x` if `y` is odd, modulo `2^b`. -/
def prodStep (b : Nat) (s : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (s.1 / 2, 2 * s.2.1 % 2 ^ b, (s.2.2 + if s.1 % 2 = 0 then 0 else s.2.1) % 2 ^ b)

theorem prod_iter (b y x : Nat) (hx : x < 2 ^ b) : ∀ k, (prodStep b)^[k] (y, x, 0) =
    (y / 2 ^ k, x * 2 ^ k % 2 ^ b, y % 2 ^ k * x % 2 ^ b)
  | 0 => by simp [Nat.mod_eq_of_lt hx, Nat.mod_one]
  | k + 1 => by
    rw [Function.iterate_succ_apply', prod_iter b y x hx k]
    unfold prodStep
    simp only [Prod.mk.injEq]
    refine ⟨by rw [Nat.div_div_eq_div_mul, Nat.pow_succ], ?_, ?_⟩
    · rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ]; grind
    · have split : y % 2 ^ (k + 1) = y % 2 ^ k + 2 ^ k * (y / 2 ^ k % 2) := by
        rw [Nat.pow_succ, Nat.mod_mul]
      rw [split]
      split
      · rename_i c; rw [c]; simp
      · rename_i c
        have c1 : y / 2 ^ k % 2 = 1 := by omega
        have e : (y % 2 ^ k + 2 ^ k * 1) * x = y % 2 ^ k * x + x * 2 ^ k := by ring
        rw [c1, e, Nat.add_mod (y % 2 ^ k * x) (x * 2 ^ k)]

end VG.Proof.Rsa.RecoverDet

namespace VG.Proof.Rsa.RecoverDet

open VG.Spec.Rsa (isqrt)

/-! ## The square root's loop -/

/-- A step of the square root, `nb`-bit remainder and root, the radicand shifted up two bits
modulo `2^wb`: its top two bits into the remainder, then `4 y + 1` subtracted if it fits. -/
def sqrtStep (nb wb : Nat) (s : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let hi := 2 * s.1 / 2 ^ wb
  let x1 := 2 * s.1 % 2 ^ wb
  let lo := 2 * x1 / 2 ^ wb
  let r := 2 * (2 * s.2.1 % 2 ^ nb + hi) % 2 ^ nb + lo
  let t := 2 * (2 * s.2.2 % 2 ^ nb) % 2 ^ nb + 1
  if r < t then (2 * x1 % 2 ^ wb, r, 2 * s.2.2 % 2 ^ nb)
  else (2 * x1 % 2 ^ wb, r - t, 2 * s.2.2 % 2 ^ nb + 1)

/-- Two bits shifted out of the top of `xs < 4 P`. -/
theorem two_bits {xs P : Nat} (hP : 0 < P) (hx : xs < 4 * P) :
    2 * (2 * xs / (4 * P)) + 2 * (2 * xs % (4 * P)) / (4 * P) = xs / P ∧
      2 * (2 * xs % (4 * P)) % (4 * P) = 4 * (xs % P) ∧
      2 * xs / (4 * P) ≤ 1 ∧ 2 * (2 * xs % (4 * P)) / (4 * P) ≤ 1 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < P ∧ xs = q * P + r := ⟨xs / P, xs % P, Nat.mod_lt _ hP,
    (Nat.div_add_mod' xs P).symm⟩
  have hq : q < 4 := by
    by_contra c
    have := Nat.mul_le_mul_right P (show 4 ≤ q by omega)
    omega
  have dP : (q * P + r) / P = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr, Nat.zero_add]
  have mP : (q * P + r) % P = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  rw [dP, mP]
  interval_cases q
  all_goals
    have d : ∀ a c, c * (4 * P) ≤ a → a < (c + 1) * (4 * P) → a / (4 * P) = c := fun a c h1 h2 =>
      Nat.div_eq_of_lt_le h1 h2
    have m : ∀ a c, c * (4 * P) ≤ a → a < (c + 1) * (4 * P) → a % (4 * P) = a - c * (4 * P) := fun a c h1 h2 => by
      rw [Nat.mod_eq_sub_mul_div, d a c h1 h2, Nat.mul_comm]
  · rw [d _ 0 (by omega) (by omega), m _ 0 (by omega) (by omega), d _ 0 (by omega) (by omega),
      m _ 0 (by omega) (by omega)]; omega
  · rw [d _ 0 (by omega) (by omega), m _ 0 (by omega) (by omega), d _ 1 (by omega) (by omega),
      m _ 1 (by omega) (by omega)]; omega
  · rw [d _ 1 (by omega) (by omega), m _ 1 (by omega) (by omega), d _ 0 (by omega) (by omega),
      m _ 0 (by omega) (by omega)]; omega
  · rw [d _ 1 (by omega) (by omega), m _ 1 (by omega) (by omega), d _ 1 (by omega) (by omega),
      m _ 1 (by omega) (by omega)]; omega

/-- What the square root's loop keeps after `i` of its `K` steps: the radicand's low
`2 (K - i)` bits at the top, and the root and remainder of the rest. -/
def SqrtInv (K X i : Nat) (s : Nat × Nat × Nat) : Prop :=
  s.1 = X % 4 ^ (K - i) * 4 ^ i ∧ s.2.2 = isqrt (X / 4 ^ (K - i)) ∧
    s.2.1 + s.2.2 * s.2.2 = X / 4 ^ (K - i)

theorem sqrtInv_step {nb K X i : Nat} {s : Nat × Nat × Nat} (hi : i < K)
    (small : isqrt X < 2 ^ nb / 8) (h : SqrtInv K X i s) :
    SqrtInv K X (i + 1) (sqrtStep nb (2 * K) s) := by
  obtain ⟨xs, r, y⟩ := s
  obtain ⟨hx, hy, hr⟩ := h
  simp only at hx hy hr
  obtain ⟨m, rfl⟩ : ∃ m, K = i + m + 1 := ⟨K - i - 1, by omega⟩
  have km : i + m + 1 - i = m + 1 := by omega
  have km' : i + m + 1 - (i + 1) = m := by omega
  rw [km] at hx hy hr
  have pos4 : ∀ j, 0 < 4 ^ j := fun j => Nat.pow_pos (by decide)
  have wb : 2 ^ (2 * (i + m + 1)) = 4 * 4 ^ (m + i) := by
    rw [Nat.pow_mul, show 2 ^ 2 = 4 by rfl, show i + m + 1 = (m + i) + 1 by omega, Nat.pow_succ,
      Nat.mul_comm]
  have eA : 4 ^ (m + 1) = 4 ^ m * 4 := by rw [Nat.pow_succ]
  have eAI : 4 ^ (m + i) = 4 ^ m * 4 ^ i := Nat.pow_add 4 m i
  have eI : 4 ^ (i + 1) = 4 ^ i * 4 := by rw [Nat.pow_succ]
  rw [eA] at hx hy hr
  generalize hA : 4 ^ m = A at *
  generalize hI : 4 ^ i = I at *
  have Apos : 0 < A := hA ▸ pos4 m
  have Ipos : 0 < I := hI ▸ pos4 i
  rw [eAI] at wb
  have xlt : xs < 4 * (A * I) := by
    rw [hx, ← Nat.mul_assoc, Nat.mul_comm 4 A]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by omega)) Ipos
  obtain ⟨bits, shifted, hb, lb⟩ := two_bits (Nat.mul_pos Apos Ipos) xlt
  have digit : xs / (A * I) = X / A % 4 := by
    rw [hx, Nat.mul_div_mul_right _ _ Ipos, Nat.mod_mul_right_div_self]
  have rest : 4 * (xs % (A * I)) = X % A * (I * 4) := by
    rw [hx, Nat.mul_mod_mul_right, Nat.mod_mul_right_mod]
    ring
  have next : X / A = 4 * (X / (A * 4)) + X / A % 4 := by
    rw [← Nat.div_div_eq_div_mul]; omega
  have yle : y ≤ isqrt X := by
    rw [hy]
    have := isqrt_spec (X / (A * 4)); have := isqrt_spec X
    have d : X / (A * 4) ≤ X := Nat.div_le_self _ _
    by_contra c
    have : (isqrt X + 1) * (isqrt X + 1) ≤ isqrt (X / (A * 4)) * isqrt (X / (A * 4)) :=
      Nat.mul_self_le_mul_self (by omega)
    omega
  have hr2 : r ≤ 2 * y := by
    have := lt_succ_isqrt_sq (X / (A * 4)); rw [← hy] at this
    have e : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by ring
    omega
  have M8 : 8 * (2 ^ nb / 8) ≤ 2 ^ nb := Nat.mul_div_le _ _
  generalize hd : X / A % 4 = δ at *
  have hδ : δ < 4 := by rw [← hd]; exact Nat.mod_lt _ (by decide)
  obtain ⟨e1, e2, _⟩ := sqrt_step (t := X / (A * 4)) (δ := δ) hy hr hδ
  have m1 : 2 * r % 2 ^ nb = 2 * r := Nat.mod_eq_of_lt (by omega)
  have m2 : 2 * (2 * r + 2 * xs / (4 * (A * I))) % 2 ^ nb =
      2 * (2 * r + 2 * xs / (4 * (A * I))) := Nat.mod_eq_of_lt (by omega)
  have m3 : 2 * y % 2 ^ nb = 2 * y := Nat.mod_eq_of_lt (by omega)
  have m4 : 2 * (2 * y) % 2 ^ nb = 2 * (2 * y) := Nat.mod_eq_of_lt (by omega)
  have R : 2 * (2 * r + 2 * xs / (4 * (A * I))) + 2 * (2 * xs % (4 * (A * I))) / (4 * (A * I)) =
      4 * r + δ := by omega
  have q1 : 2 * y * (2 * y) = 4 * (y * y) := by ring
  have q2 : (2 * y + 1) * (2 * y + 1) = 4 * (y * y) + 4 * y + 1 := by ring
  unfold sqrtStep SqrtInv
  simp only [wb, m1, m2, m3, m4, R, km', shifted, hA]
  rw [next]
  by_cases c : 4 * r + δ < 2 * (2 * y) + 1
  · have c' : ¬(4 * y + 1 ≤ 4 * r + δ) := by omega
    simp only [c, c', ↓reduceIte] at e1 e2 ⊢
    refine ⟨by rw [rest, eI], e1.symm, ?_⟩
    rw [e1] at e2; omega
  · have c' : 4 * y + 1 ≤ 4 * r + δ := by omega
    simp only [c, c', ↓reduceIte] at e1 e2 ⊢
    refine ⟨by rw [rest, eI], e1.symm, ?_⟩
    rw [e1] at e2; omega

/-- The square root's loop: `K` steps from `X < 4^K` give `isqrt X` and its remainder, if
the root has at most `nb - 3` bits. -/
theorem sqrt_iter {nb K X : Nat} (hX : X < 4 ^ K) (small : isqrt X < 2 ^ nb / 8) :
    ((sqrtStep nb (2 * K))^[K] (X, 0, 0)).2.2 = isqrt X ∧
      ((sqrtStep nb (2 * K))^[K] (X, 0, 0)).2.1 + isqrt X * isqrt X = X := by
  have go : ∀ i ≤ K, SqrtInv K X i ((sqrtStep nb (2 * K))^[i] (X, 0, 0)) := by
    intro i
    induction i with
    | zero =>
      intro _
      have z : isqrt 0 = 0 := by rw [isqrt]; simp
      refine ⟨?_, ?_, ?_⟩ <;> simp [Nat.mod_eq_of_lt hX, Nat.div_eq_of_lt hX, z]
    | succ i ih =>
      intro hi
      rw [Function.iterate_succ_apply']
      exact sqrtInv_step (by omega) small (ih (by omega))
  obtain ⟨_, hy, hr⟩ := go K (Nat.le_refl _)
  simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hy hr
  rw [← hy]
  exact ⟨rfl, hr⟩

end VG.Proof.Rsa.RecoverDet
