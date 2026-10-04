import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Almost Montgomery multiplication in radix `2⁵²`

The arithmetic of AVX512_IFMA's Montgomery multiplication, on natural
numbers: twenty limbs (`L j` for `j < 20`) whose value is
`Σ L j 2^(52 j)` (`lval`), each limb a sum of 52-bit halves of products,
never reduced below `2⁵²` until the end.

A step (`step`) for the limb `b` of the second operand: the low halves of
`a_j b` into limb `j`; `u = (L₀ k₀) mod 2⁵²`; the low halves of `m_j u`;
the carry of limb 0 into limb 1; the limbs shifted down one; and the high
halves of `a_j b` and `m_j u` into limb `j`. With `m₀ k₀ ≡ -1 (mod 2⁵²)`
the value goes from `V` to `(V + a b + u m) / 2⁵²` exactly (`step_val`),
and twenty steps from 0 give `(a b + Q m) / 2¹⁰⁴⁰` for some `Q < 2¹⁰⁴⁰`
(`steps_val`), below `2 m` for `a, b < 2 m` and `4 m ≤ 2¹⁰⁴⁰`.
-/

namespace VG.Proof.Bignum.Amm52

/-- The low and high 52 bits of the product of the low 52 bits of `x` and `y`. -/
def lo (x y : Nat) : Nat := x % 2 ^ 52 * (y % 2 ^ 52) % 2 ^ 52
def hi (x y : Nat) : Nat := x % 2 ^ 52 * (y % 2 ^ 52) / 2 ^ 52

theorem lo_lt (x y : Nat) : lo x y < 2 ^ 52 := Nat.mod_lt _ (by decide)

theorem hi_lt (x y : Nat) : hi x y < 2 ^ 52 := by
  unfold hi
  have hx := Nat.mod_lt x (show 0 < 2 ^ 52 by decide)
  have hy := Nat.mod_lt y (show 0 < 2 ^ 52 by decide)
  refine Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by decide)) ?_)
  exact Nat.le_refl _

theorem lo_hi {x y : Nat} (hx : x < 2 ^ 52) (hy : y < 2 ^ 52) : lo x y + 2 ^ 52 * hi x y = x * y := by
  unfold lo hi
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  exact Nat.mod_add_div _ _

/-- The value of the limbs below `n`. -/
def lval (L : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => lval L n + L n * 2 ^ (52 * n)

theorem lval_zero (L : Nat → Nat) : lval L 0 = 0 := rfl
theorem lval_succ (L : Nat → Nat) (n : Nat) : lval L (n + 1) = lval L n + L n * 2 ^ (52 * n) := rfl

-- Unfolding `lval` of 20 limbs computes `2 ^ (52 j)`: keep definitional
-- unfolding out of the proofs (they use `lval_zero` and `lval_succ`).
attribute [irreducible] lval

theorem lval_succ_of {L : Nat → Nat} {n : Nat} (h : L n = 0) : lval L (n + 1) = lval L n := by
  rw [lval_succ, h, Nat.zero_mul, Nat.add_zero]

theorem lval_congr {L L' : Nat → Nat} {n : Nat} (h : ∀ j < n, L j = L' j) : lval L n = lval L' n := by
  induction n with
  | zero => rw [lval_zero, lval_zero]
  | succ n ih => rw [lval_succ, lval_succ, ih fun j hj => h j (by omega), h n (by omega)]

theorem lval_add (L L' : Nat → Nat) (n : Nat) :
    lval (fun j => L j + L' j) n = lval L n + lval L' n := by
  induction n with
  | zero => simp only [lval_zero]
  | succ n ih => rw [lval_succ, lval_succ, lval_succ, ih, Nat.add_mul]; omega

theorem lval_mul (L : Nat → Nat) (c n : Nat) : lval (fun j => L j * c) n = lval L n * c := by
  induction n with
  | zero => simp only [lval_zero, Nat.zero_mul]
  | succ n ih => rw [lval_succ, lval_succ, ih, Nat.add_mul, Nat.mul_right_comm]

/-- Shifted down one limb: `lval L (n + 1) = L 0 + 2⁵² lval (L (· + 1)) n`. -/
theorem lval_succ_shift (L : Nat → Nat) (n : Nat) :
    lval L (n + 1) = L 0 + 2 ^ 52 * lval (fun j => L (j + 1)) n := by
  induction n with
  | zero => simp only [lval_succ, lval_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
  | succ n ih =>
    rw [lval_succ, ih, lval_succ, show 52 * (n + 1) = 52 * n + 52 by omega, Nat.pow_add]
    grind

theorem lval_lt {L : Nat → Nat} {n : Nat} (h : ∀ j < n, L j < 2 ^ 52) : lval L n < 2 ^ (52 * n) := by
  induction n with
  | zero => rw [lval_zero]; exact Nat.two_pow_pos _
  | succ n ih =>
    have := ih fun j hj => h j (by omega)
    have hn := h n (by omega)
    rw [lval_succ, show 52 * (n + 1) = 52 * n + 52 by omega, Nat.pow_add]
    have : L n * 2 ^ (52 * n) ≤ (2 ^ 52 - 1) * 2 ^ (52 * n) := Nat.mul_le_mul_right _ (by omega)
    have : (2 ^ 52 - 1) * 2 ^ (52 * n) + 2 ^ (52 * n) = 2 ^ (52 * n) * 2 ^ 52 := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
      have : 2 ^ (52 * n) ≤ 2 ^ (52 * n) * 2 ^ 52 := Nat.le_mul_of_pos_right _ (by decide)
      omega
    omega

/-- The operands of a multiplication: the limbs of `a` and of the modulus,
and `k₀ = -m⁻¹ mod 2⁵²`. -/
structure Ops where
  a : Nat → Nat
  m : Nat → Nat
  k0 : Nat

/-- `u` for the limb `b`. -/
def stepU (o : Ops) (L : Nat → Nat) (b : Nat) : Nat := lo (L 0 + lo (o.a 0) b) o.k0

/-- The limbs after the low halves. -/
def low (o : Ops) (L : Nat → Nat) (b : Nat) (j : Nat) : Nat :=
  L j + lo (o.a j) b + lo (o.m j) (stepU o L b)

/-- Limbs shifted down one (of twenty), with the carry of limb 0 added to
limb 1, which becomes limb 0. -/
def shifted (l : Nat → Nat) (j : Nat) : Nat :=
  if j < 19 then l (j + 1) + (if j = 0 then l 0 / 2 ^ 52 else 0) else 0

/-- A step, for the limb `b` (of twenty limbs). -/
def step (o : Ops) (L : Nat → Nat) (b : Nat) (j : Nat) : Nat :=
  shifted (low o L b) j + hi (o.a j) b + hi (o.m j) (stepU o L b)

theorem shifted_val {l : Nat → Nat} (h0 : l 0 % 2 ^ 52 = 0) : lval (shifted l) 20 * 2 ^ 52 = lval l 20 := by
  rw [lval_succ_shift l 19]
  have e1 : lval (shifted l) 20 = lval (shifted l) 19 := lval_succ_of (n := 19) (by simp [shifted])
  have e2 : lval (shifted l) 19 = lval (fun j => l (j + 1)) 19 + lval (fun j => if j = 0 then l 0 / 2 ^ 52 else 0) 19 := by
    rw [← lval_add]; exact lval_congr fun j hj => by simp only [shifted, hj, ite_true]
  have e3 : ∀ n, lval (fun j => if j = 0 then l 0 / 2 ^ 52 else 0) (n + 1) = l 0 / 2 ^ 52 := by
    intro n; induction n with
    | zero => rw [lval_succ, lval_zero, ite_eq_left rfl, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    | succ n ih => rw [lval_succ, ih, ite_eq_right (by omega), Nat.zero_mul, Nat.add_zero]
  rw [e1, e2, e3 18]
  have := Nat.div_add_mod (l 0) (2 ^ 52)
  rw [h0] at this
  rw [Nat.add_mul, Nat.mul_comm (lval _ 19)]
  omega

/-- Operands of 52-bit limbs, with `m₀ k₀ ≡ -1 (mod 2⁵²)`. -/
structure Ops.Ok (o : Ops) : Prop where
  a : ∀ j < 20, o.a j < 2 ^ 52
  m : ∀ j < 20, o.m j < 2 ^ 52
  k0 : (o.m 0 * o.k0 + 1) % 2 ^ 52 = 0

/-- Limb 0 after the low halves is a multiple of `2⁵²`. -/
theorem low0_dvd {o : Ops} (ho : o.Ok) (L : Nat → Nat) (b : Nat) : low o L b 0 % 2 ^ 52 = 0 := by
  have hm := ho.m 0 (by decide)
  have hk := ho.k0
  unfold low stepU lo
  generalize L 0 + o.a 0 % 2 ^ 52 * (b % 2 ^ 52) % 2 ^ 52 = x
  rw [Nat.mod_eq_of_lt hm, Nat.mod_mod]
  -- `m₀ (x k₀ mod 2⁵²) ≡ m₀ k₀ x ≡ -x`.
  have e : o.m 0 * (x % 2 ^ 52 * (o.k0 % 2 ^ 52) % 2 ^ 52) % 2 ^ 52 = o.m 0 * o.k0 * x % 2 ^ 52 := by
    rw [Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_mod_mod, Nat.mul_right_comm, Nat.mul_mod_mod,
      Nat.mul_right_comm]
  calc (x + o.m 0 * (x % 2 ^ 52 * (o.k0 % 2 ^ 52) % 2 ^ 52) % 2 ^ 52) % 2 ^ 52
      = (x + o.m 0 * o.k0 * x % 2 ^ 52) % 2 ^ 52 := by rw [e]
    _ = (x * (o.m 0 * o.k0 + 1)) % 2 ^ 52 := by rw [Nat.add_mod_mod]; congr 1; grind
    _ = 0 := by rw [Nat.mul_mod, hk, Nat.mul_zero, Nat.zero_mod]

/-- The value equation of a step. -/
theorem step_val {o : Ops} (ho : o.Ok) (L : Nat → Nat) {b : Nat} (hb : b < 2 ^ 52) :
    lval (step o L b) 20 * 2 ^ 52 =
      lval L 20 + lval o.a 20 * b + lval o.m 20 * stepU o L b := by
  have hu : stepU o L b < 2 ^ 52 := lo_lt _ _
  have hl : lval (low o L b) 20 =
      lval L 20 + lval (fun j => lo (o.a j) b) 20 + lval (fun j => lo (o.m j) (stepU o L b)) 20 := by
    rw [← lval_add, ← lval_add]; rfl
  have ha : lval (fun j => lo (o.a j) b) 20 + lval (fun j => hi (o.a j) b) 20 * 2 ^ 52 = lval o.a 20 * b := by
    rw [← lval_mul, ← lval_add, ← lval_mul]
    exact lval_congr fun j hj => by rw [Nat.mul_comm (hi _ _), lo_hi (ho.a j hj) hb]
  have hm : lval (fun j => lo (o.m j) (stepU o L b)) 20 + lval (fun j => hi (o.m j) (stepU o L b)) 20 * 2 ^ 52 =
      lval o.m 20 * stepU o L b := by
    rw [← lval_mul, ← lval_add, ← lval_mul]
    exact lval_congr fun j hj => by rw [Nat.mul_comm (hi _ _), lo_hi (ho.m j hj) hu]
  have hs : step o L b = fun j => (fun j => shifted (low o L b) j + hi (o.a j) b) j + hi (o.m j) (stepU o L b) := rfl
  rw [hs, lval_add, lval_add, Nat.add_mul, Nat.add_mul, shifted_val (low0_dvd ho L b), hl]
  omega

/-- A bound on the limbs kept by a step: below `S` before, below `S + 2⁵⁶`
after, while `S ≤ 2⁶²`. -/
theorem step_lt {o : Ops} {L : Nat → Nat} {b S : Nat} (hS : S ≤ 2 ^ 62) (hL : ∀ j < 20, L j < S) :
    ∀ j < 20, step o L b j < S + 2 ^ 56 := by
  intro j hj
  have hl : ∀ j < 20, low o L b j < S + 2 ^ 53 := fun j hj => by
    have := hL j hj; have := lo_lt (o.a j) b; have := lo_lt (o.m j) (stepU o L b)
    unfold low; omega
  have hc : low o L b 0 / 2 ^ 52 ≤ 2 ^ 11 := by
    have := hl 0 (by decide)
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  have := hi_lt (o.a j) b
  have := hi_lt (o.m j) (stepU o L b)
  unfold step shifted
  split
  · have := hl (j + 1) (by omega)
    split <;> omega
  · omega

/-- The steps for the limbs `b 0, …, b (n - 1)` from `L`. -/
def steps (o : Ops) (b : Nat → Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, L => L
  | n + 1, L => step o (steps o b n L) (b n)

/-- The `u` of each step. -/
def stepsU (o : Ops) (b : Nat → Nat) (L : Nat → Nat) (n : Nat) : Nat := stepU o (steps o b n L) (b n)

theorem steps_alg {X V P L0 A M lb lu bn un : Nat} (hX : X = V + A * bn + M * un)
    (h : V * P = L0 + A * lb + M * lu) : X * P = L0 + A * (lb + bn * P) + M * (lu + un * P) := by
  subst hX
  rw [Nat.add_mul, Nat.add_mul, h, Nat.mul_add, Nat.mul_add, Nat.mul_assoc, Nat.mul_assoc]
  omega

theorem steps_val {o : Ops} (ho : o.Ok) {b : Nat → Nat} (hb : ∀ i < 20, b i < 2 ^ 52) (L : Nat → Nat) :
    ∀ n ≤ 20, lval (steps o b n L) 20 * 2 ^ (52 * n) =
      lval L 20 + lval o.a 20 * lval b n + lval o.m 20 * lval (stepsU o b L) n := by
  intro n
  induction n with
  | zero =>
    intro
    have h0 : steps o b 0 L = L := rfl
    rw [h0, lval_zero, lval_zero]
    omega
  | succ n ih =>
    intro hn
    have e := step_val ho (steps o b n L) (hb n (by omega))
    have hs : steps o b (n + 1) L = step o (steps o b n L) (b n) := rfl
    have hu : stepsU o b L n = stepU o (steps o b n L) (b n) := rfl
    rw [hs, show 52 * (n + 1) = 52 + 52 * n by omega, Nat.pow_add, ← Nat.mul_assoc, lval_succ b n,
      lval_succ (stepsU o b L) n, hu]
    exact steps_alg e (ih (by omega))

theorem steps_lt {o : Ops} {b : Nat → Nat} {L : Nat → Nat} (hL : ∀ j < 20, L j < 2 ^ 56) :
    ∀ n ≤ 20, ∀ j < 20, steps o b n L j < (n + 1) * 2 ^ 56 := by
  intro n
  induction n with
  | zero => intro _ j hj; rw [Nat.zero_add, Nat.one_mul]; exact hL j hj
  | succ n ih =>
    intro hn j hj
    have h := step_lt (o := o) (b := b n) (S := (n + 1) * 2 ^ 56) (by omega) (ih (by omega)) j hj
    rw [show (n + 1 + 1) * 2 ^ 56 = (n + 1) * 2 ^ 56 + 2 ^ 56 by rw [Nat.add_mul, Nat.one_mul]]
    exact h

/-! ## Twenty steps -/

/-- Twenty steps from zero: `V 2¹⁰⁴⁰ = a b + Q m` with `Q < 2¹⁰⁴⁰` (`2^(52·20)`). -/
theorem amm_val {o : Ops} (ho : o.Ok) {b : Nat → Nat} (hb : ∀ i < 20, b i < 2 ^ 52) :
    lval (steps o b 20 fun _ => 0) 20 * 2 ^ (52 * 20) =
      lval o.a 20 * lval b 20 + lval o.m 20 * lval (stepsU o b fun _ => 0) 20 ∧
      lval (stepsU o b fun _ => 0) 20 < 2 ^ (52 * 20) := by
  have e := steps_val ho hb (fun _ => 0) 20 (Nat.le_refl _)
  have z : lval (fun _ => 0) 20 = 0 := by
    rw [show (fun _ : Nat => 0) = fun j => (fun _ : Nat => 0) j * 0 by funext; rfl, lval_mul, Nat.mul_zero]
  rw [z, Nat.zero_add] at e
  exact ⟨e, lval_lt (n := 20) fun j _ => lo_lt _ _⟩

/-- The bound of an almost Montgomery product: below `2 M` for `A, B < 2 M`
and `4 M ≤ R` (`R = 2¹⁰⁴⁰`). -/
theorem amm_lt {V A B M Q R : Nat} (h : V * R = A * B + M * Q) (hQ : Q < R)
    (hA : A < 2 * M) (hB : B < 2 * M) (hM : 4 * M ≤ R) : V < 2 * M := by
  have h1 : A * B ≤ 4 * M * M := by
    have := Nat.mul_le_mul (Nat.le_of_lt hA) (Nat.le_of_lt hB)
    calc A * B ≤ 2 * M * (2 * M) := this
      _ = 4 * M * M := by grind
  have h2 : 4 * M * M ≤ R * M := Nat.mul_le_mul_right _ hM
  have h3 : M * Q + M ≤ M * R := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hQ
  have : V * R < 2 * M * R := by
    rw [h]
    have e : 2 * M * R = R * M + M * R := by grind
    rw [e]
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · omega
    · omega
  exact Nat.lt_of_mul_lt_mul_right this

/-! ## Carrying -/

/-- The carry into limb `j`, carrying the limbs in order. -/
def carryIn (L : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (L j + carryIn L j) / 2 ^ 52

/-- The limbs carried. -/
def carried (L : Nat → Nat) (j : Nat) : Nat := (L j + carryIn L j) % 2 ^ 52

theorem carried_lt (L : Nat → Nat) (j : Nat) : carried L j < 2 ^ 52 := Nat.mod_lt _ (by decide)

theorem carried_val (L : Nat → Nat) (n : Nat) :
    lval (carried L) n + carryIn L n * 2 ^ (52 * n) = lval L n := by
  induction n with
  | zero => rw [lval_zero, lval_zero, show carryIn L 0 = 0 from rfl]
  | succ n ih =>
    rw [lval_succ, lval_succ, ← ih]
    have e := Nat.div_add_mod (L n + carryIn L n) (2 ^ 52)
    have hc : carryIn L (n + 1) = (L n + carryIn L n) / 2 ^ 52 := rfl
    have hr : carried L n = (L n + carryIn L n) % 2 ^ 52 := rfl
    rw [hc, hr, show 52 * (n + 1) = 52 * n + 52 by omega, Nat.pow_add]
    generalize (L n + carryIn L n) / 2 ^ 52 = q at e ⊢
    generalize (L n + carryIn L n) % 2 ^ 52 = r at e ⊢
    generalize 2 ^ (52 * n) = P
    generalize lval (carried L) n = X
    have : (L n + carryIn L n) * P = (2 ^ 52 * q + r) * P := by rw [e]
    grind

/-- Carries stay below `2¹⁰` for limbs below `2⁶¹`. -/
theorem carryIn_lt {L : Nat → Nat} {n : Nat} (h : ∀ j < n, L j < 2 ^ 61) : carryIn L n < 2 ^ 10 := by
  induction n with
  | zero => simp only [carryIn]; decide
  | succ n ih =>
    have := ih fun j hj => h j (by omega)
    have := h n (by omega)
    simp only [carryIn]
    exact Nat.div_lt_of_lt_mul (by omega)

/-- Twenty limbs of a value below `2¹⁰⁴⁰` leave no carry. -/
theorem carryIn_zero {L : Nat → Nat} (h : lval L 20 < 2 ^ (52 * 20)) : carryIn L 20 = 0 := by
  have e := carried_val L 20
  generalize 2 ^ (52 * 20) = R at e h
  rcases Nat.eq_zero_or_pos (carryIn L 20) with h0 | h0
  · exact h0
  · exfalso
    have : R ≤ carryIn L 20 * R := Nat.le_mul_of_pos_left _ h0
    omega

end VG.Proof.Bignum.Amm52
