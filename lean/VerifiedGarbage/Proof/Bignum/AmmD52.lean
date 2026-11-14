module

public import VerifiedGarbage.Proof.Bignum.Amm52N
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Almost Montgomery multiplication in radix `2⁵²` whose quotient digit is limb 0

A multiplication for a modulus `X` with `X + 1` a multiple of `2¹⁰⁴`, as the
code of `Impl/Rsa/X86_64/CrtIfma.lean` (`ammCoreZ`) runs it, limb by limb:
with `ms` the limbs of `X + 1` (so `ms 0 = ms 1 = 0`), a step for the limb
`b` of the second operand takes limb 0's low 52 bits as the quotient digit
`q` (no multiplication by `-X⁻¹`, which is 1) and adds `a b + q X = a b + q
(X + 1) - q`.

The limbs are in rows of `R`, limb `j` in row `j % R` (the stride layout),
and in two sets: `bs`, which the products of `b` go to, and `us`, which the
products of `q` go to. A step

* adds the two sets' row 0 (`rsum`, with the low halves of `a b`), whose
  limb 0 gives `q`, and carries each of its limbs: the bits from 52 up go
  to the limb above (`bs`), and the low 52 bits (but limb 0's, which `- q`
  cancels) become the row above the others, a limb down (`us`);
* shifts every other row down, adding the products' halves.

The products of `q` that belong in the new row 0 are left for the next step
(`pend`), which adds them once that row has been carried, so that `q`'s
products are not needed before the next `q`: the limbs stand for `tot`, the
two sets and what is pending, and `step_val` is `Amm52N.step_val` for it:
the value goes from `V` to `(V + a b + q X) / 2⁵²` exactly, so `N` steps
from 0 give `(a b + Q X) / 2^(52 N)` for some `Q < 2^(52 N)` (`steps_val`),
which `Amm52.amm_lt` bounds.
-/
-- separate module: the arithmetic names no ISA, so that another target's multiplication of this shape can use it.

@[expose] public section

namespace VG.Proof.Bignum.AmmD52

open VG.Proof.Bignum.Amm52 (lo hi lo_lt hi_lt lo_hi lval lval_zero lval_succ lval_congr lval_add lval_mul)

/-- The first operand's limbs, and those of the modulus plus one. -/
structure Ops where
  a : Nat → Nat
  ms : Nat → Nat

/-- The limbs of the two sets, and the last quotient digit. -/
structure St where
  bs : Nat → Nat
  us : Nat → Nat
  qp : Nat

/-- The products of the last quotient digit not added yet: those of row 0. -/
def pend (R : Nat) (o : Ops) (qp : Nat) (j : Nat) : Nat :=
  if j % R = 0 then hi (o.ms j) qp + lo (o.ms (j + 1)) qp else 0

/-- Limb `j` with the low half of `a b`. -/
def lowS (o : Ops) (s : St) (b : Nat) (j : Nat) : Nat := s.bs j + lo (o.a j) b + s.us j

/-- The quotient digit for the limb `b`: the low 52 bits of limb 0. -/
def stepQ (o : Ops) (s : St) (b : Nat) : Nat := lowS o s b 0 % 2 ^ 52

/-- A step, for the limb `b` (of `N` limbs in rows of `R`). -/
def step (N R : Nat) (o : Ops) (s : St) (b : Nat) : St where
  bs j :=
    if j % R = 0 then s.bs (j + 1) + lo (o.a (j + 1)) b + hi (o.a j) b + lowS o s b j / 2 ^ 52
    else if (j + 1) % R = 0 then hi (o.a j) b
    else s.bs (j + 1) + lo (o.a (j + 1)) b + hi (o.a j) b
  us j :=
    if j % R = 0 then s.us (j + 1)
    else if (j + 1) % R = 0 then
      (if j + 1 < N then lowS o s b (j + 1) % 2 ^ 52 + pend R o s.qp (j + 1) + lo (o.ms (j + 1)) (stepQ o s b)
        else 0) + hi (o.ms j) (stepQ o s b)
    else s.us (j + 1) + lo (o.ms (j + 1)) (stepQ o s b) + hi (o.ms j) (stepQ o s b)
  qp := stepQ o s b

/-- The limbs the two sets stand for. -/
def tot (R : Nat) (o : Ops) (s : St) (j : Nat) : Nat := s.bs j + s.us j + pend R o s.qp j

/-- Operands of `N` limbs of 52 bits, with limbs 0 and 1 of the modulus
plus one zero. -/
structure Ok (N : Nat) (o : Ops) : Prop where
  a : ∀ j < N, o.a j < 2 ^ 52
  ms : ∀ j < N, o.ms j < 2 ^ 52
  ms0 : o.ms 0 = 0
  ms1 : o.ms 1 = 0

theorem lo_zero (y : Nat) : lo 0 y = 0 := by
  unfold lo; rw [Nat.zero_mod, Nat.zero_mul, Nat.zero_mod]

theorem hi_zero (y : Nat) : hi 0 y = 0 := by
  unfold hi; rw [Nat.zero_mod, Nat.zero_mul, Nat.zero_div]

/-- Limbs `u + v` shifted down one, with `u`'s limbs of row 0 carried: their
bits from 52 up to the limb above, their low 52 bits kept (limb 0's
dropped). -/
def shiftC (N R : Nat) (u v : Nat → Nat) (j : Nat) : Nat :=
  (if j + 1 < N then (if (j + 1) % R = 0 then u (j + 1) % 2 ^ 52 else u (j + 1)) + v (j + 1) else 0) +
    (if j % R = 0 then u j / 2 ^ 52 else 0)

theorem shiftC_val {N R : Nat} (hR : 2 ≤ R) (hN : 0 < N) (hd : N % R = 0) (u v : Nat → Nat) :
    lval (shiftC N R u v) N * 2 ^ 52 + u 0 % 2 ^ 52 + v 0 = lval (fun j => u j + v j) N := by
  have key : ∀ n, n < N → lval (shiftC N R u v) n * 2 ^ 52 + u 0 % 2 ^ 52 + v 0 +
      (if n % R = 0 then u n / 2 ^ 52 * 2 ^ 52 * 2 ^ (52 * n) else 0) = lval (fun j => u j + v j) (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      have e0 : (0 : Nat) % R = 0 := Nat.zero_mod R
      simp only [lval_zero, lval_succ, e0, ↓reduceIte, Nat.mul_zero, Nat.pow_zero, Nat.zero_mul, Nat.zero_add,
        Nat.mul_one]
      have := Nat.div_add_mod' (u 0) (2 ^ 52)
      omega_using []
    | succ n ih =>
      intro hn
      have h := ih (by omega_using [hn])
      rw [lval_succ, lval_succ (fun j => u j + v j) (n + 1), ← h]
      have hp : 2 ^ (52 * (n + 1)) = 2 ^ 52 * 2 ^ (52 * n) := by
        rw [show 52 * (n + 1) = 52 + 52 * n by omega_using [], Nat.pow_add]
      have hs : shiftC N R u v n =
          (if (n + 1) % R = 0 then u (n + 1) % 2 ^ 52 else u (n + 1)) + v (n + 1) +
            (if n % R = 0 then u n / 2 ^ 52 else 0) := by
        unfold shiftC; rw [ite_eq_left hn]
      rw [hs, hp]
      have hm := Nat.div_add_mod' (u (n + 1)) (2 ^ 52)
      generalize 2 ^ (52 * n) = P
      generalize lval (shiftC N R u v) n = A
      generalize (2 : Nat) ^ 52 = W at hm ⊢
      generalize u (n + 1) / W = c1 at hm ⊢
      generalize u (n + 1) % W = r1 at hm ⊢
      generalize u (n + 1) = u1 at hm ⊢
      generalize u n / W = c0
      generalize u 0 % W = r0
      subst hm
      by_cases h0 : n % R = 0 <;> by_cases h1 : (n + 1) % R = 0
      · rw [ite_eq_left h0, ite_eq_left h0, ite_eq_left h1, ite_eq_left h1]; grind
      · rw [ite_eq_left h0, ite_eq_left h0, ite_eq_right h1, ite_eq_right h1]; grind
      · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_left h1, ite_eq_left h1]; grind
      · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_right h1, ite_eq_right h1]; grind
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega_using [hN]⟩
  have hl : shiftC (n + 1) R u v n = 0 := by
    unfold shiftC
    rw [ite_eq_right (by omega_using []), ite_eq_right (by
      intro h; have := Nat.mod_eq_of_lt (show 1 < R by omega_using [hR])
      have h2 : (n + 1) % R = (n % R + 1 % R) % R := Nat.add_mod _ _ _
      rw [h, this, Nat.zero_add, this] at h2; omega_using [hd, h2])]
  have h := key n (by omega_using [])
  rw [lval_succ, hl, Nat.zero_mul, Nat.add_zero]
  have hnr : ¬ n % R = 0 := by
    intro h0
    have h2 : (n + 1) % R = (n % R + 1 % R) % R := Nat.add_mod _ _ _
    rw [h0, Nat.mod_eq_of_lt (show 1 < R by omega_using [hR]), Nat.zero_add, Nat.mod_eq_of_lt (show 1 < R by omega_using [hR])] at h2
    omega_using [hd, h2]
  rw [ite_eq_right hnr, Nat.add_zero] at h
  exact h

/-- The limbs after a step are those before, with the halves of `a b` and
of `q (X + 1)`, shifted and carried. -/
theorem tot_step {N R : Nat} (hR : 2 ≤ R) (hd : N % R = 0) (o : Ops) (s : St) (b : Nat) {j : Nat} (hj : j < N) :
    tot R o (step N R o s b) j =
      shiftC N R (lowS o s b) (fun j => pend R o s.qp j + lo (o.ms j) (stepQ o s b)) j +
        hi (o.a j) b + hi (o.ms j) (stepQ o s b) := by
  have h1 : 1 % R = 1 := Nat.mod_eq_of_lt (by omega_using [hR])
  have hsucc : ∀ m, (m + 1) % R = (m % R + 1) % R := fun m => by rw [Nat.add_mod, h1]
  simp only [tot, step, shiftC, pend]
  by_cases h0 : j % R = 0
  · have hn1 : ¬ (j + 1) % R = 0 := by rw [hsucc, h0, Nat.zero_add, h1]; omega_using []
    have hlt : j + 1 < N := by
      rcases Nat.lt_or_ge (j + 1) N with h | h
      · exact h
      · exfalso; have : j + 1 = N := by omega_using [hj, h]
        rw [this] at hn1; exact hn1 hd
    simp only [h0, hn1, hlt, ite_true, ite_false, lowS]
    omega_using []
  · by_cases hn1 : (j + 1) % R = 0
    · simp only [h0, hn1, ite_true, ite_false]
      split <;> omega_using []
    · have hlt : j + 1 < N := by
        rcases Nat.lt_or_ge (j + 1) N with h | h
        · exact h
        · exfalso; have : j + 1 = N := by omega_using [hj, h]
          rw [this] at hn1; exact hn1 hd
      simp only [h0, hn1, hlt, ite_true, ite_false, lowS]
      omega_using []

theorem val_alg {SH W q T La Lm Ha Hm PA PM : Nat} (hv : SH * W + q = T + La + Lm) (ha : La + Ha * W = PA)
    (hm : Lm + Hm * W = PM) : SH * W + Ha * W + Hm * W + q = T + PA + PM := by omega_using [hv, ha, hm]

/-- The value equation of a step: with `X + 1 = lval o.ms N`, the value
times `2⁵²` is the value before plus `a b + q X`. -/
theorem step_val {N R : Nat} (hR : 2 ≤ R) (hN : 0 < N) (hd : N % R = 0) {o : Ops} (ho : Ok N o) (s : St)
    {b : Nat} (hb : b < 2 ^ 52) :
    lval (tot R o (step N R o s b)) N * 2 ^ 52 + stepQ o s b =
      lval (tot R o s) N + lval o.a N * b + lval o.ms N * stepQ o s b := by
  have hq : stepQ o s b < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have h1 : 1 % R = 1 := Nat.mod_eq_of_lt (by omega_using [hR])
  have ha : lval (fun j => lo (o.a j) b) N + lval (fun j => hi (o.a j) b) N * 2 ^ 52 = lval o.a N * b := by
    rw [← lval_mul, ← lval_add, ← lval_mul]
    exact lval_congr fun j hj => by rw [Nat.mul_comm (hi _ _), lo_hi (ho.a j hj) hb]
  have hm : lval (fun j => lo (o.ms j) (stepQ o s b)) N + lval (fun j => hi (o.ms j) (stepQ o s b)) N * 2 ^ 52 =
      lval o.ms N * stepQ o s b := by
    rw [← lval_mul, ← lval_add, ← lval_mul]
    exact lval_congr fun j hj => by rw [Nat.mul_comm (hi _ _), lo_hi (ho.ms j hj) hq]
  have hs : lval (tot R o (step N R o s b)) N =
      lval (fun j => (fun j => shiftC N R (lowS o s b) (fun j => pend R o s.qp j + lo (o.ms j) (stepQ o s b)) j +
        hi (o.a j) b) j + hi (o.ms j) (stepQ o s b)) N :=
    lval_congr fun j hj => tot_step hR hd o s b hj
  have hv := shiftC_val hR hN hd (lowS o s b) (fun j => pend R o s.qp j + lo (o.ms j) (stepQ o s b))
  have hv0 : pend R o s.qp 0 + lo (o.ms 0) (stepQ o s b) = 0 := by
    have e0 : (0 : Nat) % R = 0 := Nat.zero_mod R
    have e1 : o.ms (0 + 1) = 0 := ho.ms1
    simp only [pend, e0, ↓reduceIte, ho.ms0, e1, hi_zero, lo_zero]
  have hsum : lval (fun j => lowS o s b j + (pend R o s.qp j + lo (o.ms j) (stepQ o s b))) N =
      lval (tot R o s) N + lval (fun j => lo (o.a j) b) N + lval (fun j => lo (o.ms j) (stepQ o s b)) N := by
    rw [← lval_add, ← lval_add]
    exact lval_congr fun j _ => by simp only [lowS, tot]; omega_using []
  rw [hs, lval_add, lval_add, Nat.add_mul, Nat.add_mul]
  simp only [hv0, Nat.add_zero] at hv
  rw [hsum] at hv
  exact val_alg hv ha hm

/-- A bound on the limbs kept by a step: below `S` before, below `S + 2⁵⁶`
after, while `S ≤ 2⁶²`. -/
theorem step_lt {N R : Nat} {o : Ops} {s : St} {b S : Nat} (hS : S ≤ 2 ^ 62)
    (hB : ∀ j, s.bs j < S) (hU : ∀ j, s.us j < S) :
    (∀ j, (step N R o s b).bs j < S + 2 ^ 56) ∧ (∀ j, (step N R o s b).us j < S + 2 ^ 56) := by
  have hl : ∀ j, lowS o s b j < 2 * S + 2 ^ 52 := fun j => by
    have := hB j; have := hU j; have := lo_lt (o.a j) b
    unfold lowS; omega_arith
  have hc : ∀ j, lowS o s b j / 2 ^ 52 < 2 ^ 12 := fun j =>
    Nat.div_lt_of_lt_mul (by have := hl j; omega_using [hS, this])
  have hp : ∀ j, pend R o s.qp j < 2 ^ 53 := fun j => by
    have := hi_lt (o.ms j) s.qp; have := lo_lt (o.ms (j + 1)) s.qp
    unfold pend; split <;> omega_arith
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := hB (j + 1); have := lo_lt (o.a (j + 1)) b; have := hi_lt (o.a j) b; have := hc j
    show (if j % R = 0 then s.bs (j + 1) + lo (o.a (j + 1)) b + hi (o.a j) b + lowS o s b j / 2 ^ 52
      else if (j + 1) % R = 0 then hi (o.a j) b
      else s.bs (j + 1) + lo (o.a (j + 1)) b + hi (o.a j) b) < _
    by_cases h0 : j % R = 0
    · rw [ite_eq_left h0]; omega_arith
    · rw [ite_eq_right h0]
      by_cases h1 : (j + 1) % R = 0
      · rw [ite_eq_left h1]; omega_arith
      · rw [ite_eq_right h1]; omega_arith
  · have := hU (j + 1); have := lo_lt (o.ms (j + 1)) (stepQ o s b); have := hi_lt (o.ms j) (stepQ o s b)
    have := hp (j + 1); have := Nat.mod_lt (lowS o s b (j + 1)) (show 0 < 2 ^ 52 by decide)
    show (if j % R = 0 then s.us (j + 1)
      else if (j + 1) % R = 0 then
        (if j + 1 < N then lowS o s b (j + 1) % 2 ^ 52 + pend R o s.qp (j + 1) + lo (o.ms (j + 1)) (stepQ o s b)
          else 0) + hi (o.ms j) (stepQ o s b)
      else s.us (j + 1) + lo (o.ms (j + 1)) (stepQ o s b) + hi (o.ms j) (stepQ o s b)) < _
    by_cases h0 : j % R = 0
    · rw [ite_eq_left h0]; omega_arith
    · rw [ite_eq_right h0]
      by_cases h1 : (j + 1) % R = 0
      · rw [ite_eq_left h1]
        by_cases h2 : j + 1 < N
        · rw [ite_eq_left h2]; omega_arith
        · rw [ite_eq_right h2]; omega_arith
      · rw [ite_eq_right h1]; omega_arith

/-- The steps for the limbs `b 0, …, b (n - 1)` from `s`. -/
def steps (N R : Nat) (o : Ops) (b : Nat → Nat) : Nat → St → St
  | 0, s => s
  | n + 1, s => step N R o (steps N R o b n s) (b n)

/-- The quotient digit of each step. -/
def stepsQ (N R : Nat) (o : Ops) (b : Nat → Nat) (s : St) (n : Nat) : Nat :=
  stepQ o (steps N R o b n s) (b n)

theorem stepsQ_lt (N R : Nat) (o : Ops) (b : Nat → Nat) (s : St) (n : Nat) : stepsQ N R o b s n < 2 ^ 52 :=
  Nat.mod_lt _ (by decide)

/-- `n` steps: with `X + 1 = lval o.ms N`, the value times `2^(52 n)` is
the value before plus `a b + Q X`, for `Q` the quotient digits. -/
theorem steps_val {N R : Nat} (hR : 2 ≤ R) (hN : 0 < N) (hd : N % R = 0) {o : Ops} (ho : Ok N o)
    {b : Nat → Nat} (hb : ∀ i < N, b i < 2 ^ 52) (s : St) {X : Nat} (hX : lval o.ms N = X + 1) :
    ∀ n ≤ N, lval (tot R o (steps N R o b n s)) N * 2 ^ (52 * n) =
      lval (tot R o s) N + lval o.a N * lval b n + X * lval (stepsQ N R o b s) n := by
  intro n
  induction n with
  | zero =>
    intro
    have h0 : steps N R o b 0 s = s := rfl
    rw [h0, lval_zero, lval_zero]
    omega_using []
  | succ n ih =>
    intro hn
    have e := step_val hR hN hd ho (steps N R o b n s) (hb n (by omega_using [hn]))
    rw [hX, Nat.add_mul, Nat.one_mul] at e
    have e' : lval (tot R o (step N R o (steps N R o b n s) (b n))) N * 2 ^ 52 =
        lval (tot R o (steps N R o b n s)) N + lval o.a N * b n + X * stepQ o (steps N R o b n s) (b n) := by
      generalize lval (tot R o (step N R o (steps N R o b n s) (b n))) N * 2 ^ 52 = v at e ⊢
      generalize stepQ o (steps N R o b n s) (b n) = q at e ⊢
      generalize lval (tot R o (steps N R o b n s)) N = w at e ⊢
      generalize lval o.a N * b n = y at e ⊢
      generalize X * q = z at e ⊢
      omega_using [e]
    have hs : steps N R o b (n + 1) s = step N R o (steps N R o b n s) (b n) := rfl
    have hu : stepsQ N R o b s n = stepQ o (steps N R o b n s) (b n) := rfl
    rw [hs, show 52 * (n + 1) = 52 + 52 * n by omega_using [], Nat.pow_add, ← Nat.mul_assoc, lval_succ b n,
      lval_succ (stepsQ N R o b s) n, hu]
    exact Amm52.steps_alg e' (ih (by omega_using [hn]))

theorem steps_lt {N R : Nat} {o : Ops} {b : Nat → Nat} {s : St}
    (hB : ∀ j, s.bs j < 2 ^ 56) (hU : ∀ j, s.us j < 2 ^ 56) :
    ∀ n ≤ 63, (∀ j, (steps N R o b n s).bs j < (n + 1) * 2 ^ 56) ∧
      (∀ j, (steps N R o b n s).us j < (n + 1) * 2 ^ 56) := by
  intro n
  induction n with
  | zero => intro _; rw [Nat.zero_add, Nat.one_mul]; exact ⟨hB, hU⟩
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega_using [hn])
    have h := step_lt (N := N) (R := R) (o := o) (b := b n) (S := (n + 1) * 2 ^ 56) (by omega_using [hn]) h1 h2
    rw [show (n + 1 + 1) * 2 ^ 56 = (n + 1) * 2 ^ 56 + 2 ^ 56 by rw [Nat.add_mul, Nat.one_mul]]
    exact h

end VG.Proof.Bignum.AmmD52
