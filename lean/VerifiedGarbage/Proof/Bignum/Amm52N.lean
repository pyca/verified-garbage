import VerifiedGarbage.Proof.Bignum.Amm52

/-!
# Almost Montgomery multiplication in radix `2⁵²`, of any number of limbs

`Amm52`'s steps for numbers of `N` limbs (`N ≥ 2`) instead of twenty: a
step (`step N`) for the limb `b` of the second operand takes the value from
`V` to `(V + a b + u m) / 2⁵²` exactly (`step_val`), and `N` steps from 0
give `(a b + Q m) / 2^(52 N)` for some `Q < 2^(52 N)` (`amm_val`), below
`2 m` for `a, b < 2 m` and `4 m ≤ 2^(52 N)` (`Amm52.amm_lt`). The low halves
and `u` (`Amm52.low`, `Amm52.stepU`) do not depend on `N`.
-/

namespace VG.Proof.Bignum.Amm52N

open VG.Proof.Bignum.Amm52 (lo hi lo_lt hi_lt lo_hi lval lval_zero lval_succ lval_succ_of lval_congr
  lval_add lval_mul lval_succ_shift lval_lt Ops stepU low carryIn carried carried_val)

/-- Limbs shifted down one (of `N`), with the carry of limb 0 added to limb
1, which becomes limb 0. -/
def shifted (N : Nat) (l : Nat → Nat) (j : Nat) : Nat :=
  if j + 1 < N then l (j + 1) + (if j = 0 then l 0 / 2 ^ 52 else 0) else 0

/-- A step, for the limb `b` (of `N` limbs). -/
def step (N : Nat) (o : Ops) (L : Nat → Nat) (b : Nat) (j : Nat) : Nat :=
  shifted N (low o L b) j + hi (o.a j) b + hi (o.m j) (stepU o L b)

theorem shifted_val {N : Nat} (hN : 2 ≤ N) {l : Nat → Nat} (h0 : l 0 % 2 ^ 52 = 0) :
    lval (shifted N l) N * 2 ^ 52 = lval l N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : n ≠ 0 := by omega
  rw [lval_succ_shift l n]
  have e1 : lval (shifted (n + 1) l) (n + 1) = lval (shifted (n + 1) l) n :=
    lval_succ_of (n := n) (by simp [shifted])
  have e2 : lval (shifted (n + 1) l) n =
      lval (fun j => l (j + 1)) n + lval (fun j => if j = 0 then l 0 / 2 ^ 52 else 0) n := by
    rw [← lval_add]; exact lval_congr fun j hj => by
      simp only [shifted, show j + 1 < n + 1 by omega, ite_true]
  have e3 : ∀ k, lval (fun j => if j = 0 then l 0 / 2 ^ 52 else 0) k = if k = 0 then 0 else l 0 / 2 ^ 52 := by
    intro k; induction k with
    | zero => rw [lval_zero]; rfl
    | succ k ih =>
      rw [lval_succ, ih]
      rcases k with _ | k
      · simp
      · simp
  rw [e1, e2, e3 n]
  have := Nat.div_add_mod (l 0) (2 ^ 52)
  rw [h0] at this
  rw [Nat.add_mul, Nat.mul_comm (lval _ n)]
  simp only [hn, ite_false]
  omega

/-- Operands of `N` limbs of 52 bits, with `m₀ k₀ ≡ -1 (mod 2⁵²)`. -/
structure Ok (N : Nat) (o : Ops) : Prop where
  a : ∀ j < N, o.a j < 2 ^ 52
  m : ∀ j < N, o.m j < 2 ^ 52
  k0 : (o.m 0 * o.k0 + 1) % 2 ^ 52 = 0

/-- Limb 0 after the low halves is a multiple of `2⁵²`. -/
theorem low0_dvd {N : Nat} (hN : 1 ≤ N) {o : Ops} (ho : Ok N o) (L : Nat → Nat) (b : Nat) :
    low o L b 0 % 2 ^ 52 = 0 := by
  have hm := ho.m 0 hN
  have hk := ho.k0
  unfold low stepU lo
  generalize L 0 + o.a 0 % 2 ^ 52 * (b % 2 ^ 52) % 2 ^ 52 = x
  rw [Nat.mod_eq_of_lt hm, Nat.mod_mod]
  have e : o.m 0 * (x % 2 ^ 52 * (o.k0 % 2 ^ 52) % 2 ^ 52) % 2 ^ 52 = o.m 0 * o.k0 * x % 2 ^ 52 := by
    rw [Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_mod_mod, Nat.mul_right_comm, Nat.mul_mod_mod,
      Nat.mul_right_comm]
  calc (x + o.m 0 * (x % 2 ^ 52 * (o.k0 % 2 ^ 52) % 2 ^ 52) % 2 ^ 52) % 2 ^ 52
      = (x + o.m 0 * o.k0 * x % 2 ^ 52) % 2 ^ 52 := by rw [e]
    _ = (x * (o.m 0 * o.k0 + 1)) % 2 ^ 52 := by rw [Nat.add_mod_mod]; congr 1; grind
    _ = 0 := by rw [Nat.mul_mod, hk, Nat.mul_zero, Nat.zero_mod]

/-- The value equation of a step. -/
theorem step_val {N : Nat} (hN : 2 ≤ N) {o : Ops} (ho : Ok N o) (L : Nat → Nat) {b : Nat}
    (hb : b < 2 ^ 52) :
    lval (step N o L b) N * 2 ^ 52 = lval L N + lval o.a N * b + lval o.m N * stepU o L b := by
  have hu : stepU o L b < 2 ^ 52 := lo_lt _ _
  have hl : lval (low o L b) N =
      lval L N + lval (fun j => lo (o.a j) b) N + lval (fun j => lo (o.m j) (stepU o L b)) N := by
    rw [← lval_add, ← lval_add]; rfl
  have ha : lval (fun j => lo (o.a j) b) N + lval (fun j => hi (o.a j) b) N * 2 ^ 52 = lval o.a N * b := by
    rw [← lval_mul, ← lval_add, ← lval_mul]
    exact lval_congr fun j hj => by rw [Nat.mul_comm (hi _ _), lo_hi (ho.a j hj) hb]
  have hm : lval (fun j => lo (o.m j) (stepU o L b)) N + lval (fun j => hi (o.m j) (stepU o L b)) N * 2 ^ 52 =
      lval o.m N * stepU o L b := by
    rw [← lval_mul, ← lval_add, ← lval_mul]
    exact lval_congr fun j hj => by rw [Nat.mul_comm (hi _ _), lo_hi (ho.m j hj) hu]
  have hs : step N o L b =
      fun j => (fun j => shifted N (low o L b) j + hi (o.a j) b) j + hi (o.m j) (stepU o L b) := rfl
  rw [hs, lval_add, lval_add, Nat.add_mul, Nat.add_mul, shifted_val hN (low0_dvd (by omega) ho L b), hl]
  omega

/-- A bound on the limbs kept by a step: below `S` before, below `S + 2⁵⁶`
after, while `S ≤ 2⁶²`. -/
theorem step_lt {N : Nat} {o : Ops} {L : Nat → Nat} {b S : Nat} (hS : S ≤ 2 ^ 62)
    (hL : ∀ j < N, L j < S) : ∀ j < N, step N o L b j < S + 2 ^ 56 := by
  intro j hj
  have hl : ∀ j < N, low o L b j < S + 2 ^ 53 := fun j hj => by
    have := hL j hj; have := lo_lt (o.a j) b; have := lo_lt (o.m j) (stepU o L b)
    unfold low; omega
  have hc : low o L b 0 / 2 ^ 52 ≤ 2 ^ 11 := by
    have := hl 0 (by omega)
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  have := hi_lt (o.a j) b
  have := hi_lt (o.m j) (stepU o L b)
  unfold step shifted
  split
  · have := hl (j + 1) (by omega)
    split <;> omega
  · omega

/-- The steps for the limbs `b 0, …, b (n - 1)` from `L`. -/
def steps (N : Nat) (o : Ops) (b : Nat → Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, L => L
  | n + 1, L => step N o (steps N o b n L) (b n)

/-- The `u` of each step. -/
def stepsU (N : Nat) (o : Ops) (b : Nat → Nat) (L : Nat → Nat) (n : Nat) : Nat :=
  stepU o (steps N o b n L) (b n)

theorem steps_val {N : Nat} (hN : 2 ≤ N) {o : Ops} (ho : Ok N o) {b : Nat → Nat}
    (hb : ∀ i < N, b i < 2 ^ 52) (L : Nat → Nat) :
    ∀ n ≤ N, lval (steps N o b n L) N * 2 ^ (52 * n) =
      lval L N + lval o.a N * lval b n + lval o.m N * lval (stepsU N o b L) n := by
  intro n
  induction n with
  | zero =>
    intro
    have h0 : steps N o b 0 L = L := rfl
    rw [h0, lval_zero, lval_zero]
    omega
  | succ n ih =>
    intro hn
    have e := step_val hN ho (steps N o b n L) (hb n (by omega))
    have hs : steps N o b (n + 1) L = step N o (steps N o b n L) (b n) := rfl
    have hu : stepsU N o b L n = stepU o (steps N o b n L) (b n) := rfl
    rw [hs, show 52 * (n + 1) = 52 + 52 * n by omega, Nat.pow_add, ← Nat.mul_assoc, lval_succ b n,
      lval_succ (stepsU N o b L) n, hu]
    exact Amm52.steps_alg e (ih (by omega))

theorem steps_lt {N : Nat} {o : Ops} {b : Nat → Nat} {L : Nat → Nat} (hN : N ≤ 63)
    (hL : ∀ j < N, L j < 2 ^ 56) :
    ∀ n ≤ N, ∀ j < N, steps N o b n L j < (n + 1) * 2 ^ 56 := by
  intro n
  induction n with
  | zero => intro _ j hj; rw [Nat.zero_add, Nat.one_mul]; exact hL j hj
  | succ n ih =>
    intro hn j hj
    have h := step_lt (o := o) (b := b n) (S := (n + 1) * 2 ^ 56) (by omega) (ih (by omega)) j hj
    rw [show (n + 1 + 1) * 2 ^ 56 = (n + 1) * 2 ^ 56 + 2 ^ 56 by rw [Nat.add_mul, Nat.one_mul]]
    exact h

/-- `N` steps from zero: `V 2^(52 N) = a b + Q m` with `Q < 2^(52 N)`. -/
theorem amm_val {N : Nat} (hN : 2 ≤ N) {o : Ops} (ho : Ok N o) {b : Nat → Nat}
    (hb : ∀ i < N, b i < 2 ^ 52) :
    lval (steps N o b N fun _ => 0) N * 2 ^ (52 * N) =
      lval o.a N * lval b N + lval o.m N * lval (stepsU N o b fun _ => 0) N ∧
      lval (stepsU N o b fun _ => 0) N < 2 ^ (52 * N) := by
  have e := steps_val hN ho hb (fun _ => 0) N (Nat.le_refl _)
  have z : lval (fun _ => 0) N = 0 := by
    rw [show (fun _ : Nat => 0) = fun j => (fun _ : Nat => 0) j * 0 by funext; rfl, lval_mul, Nat.mul_zero]
  rw [z, Nat.zero_add] at e
  exact ⟨e, lval_lt (n := N) fun j _ => lo_lt _ _⟩

/-- `N` limbs of a value below `2^(52 N)` leave no carry. -/
theorem carryIn_zero {N : Nat} {L : Nat → Nat} (h : lval L N < 2 ^ (52 * N)) : carryIn L N = 0 := by
  have e := carried_val L N
  generalize 2 ^ (52 * N) = R at e h
  rcases Nat.eq_zero_or_pos (carryIn L N) with h0 | h0
  · exact h0
  · exfalso
    have : R ≤ carryIn L N * R := Nat.le_mul_of_pos_left _ h0
    omega

end VG.Proof.Bignum.Amm52N
