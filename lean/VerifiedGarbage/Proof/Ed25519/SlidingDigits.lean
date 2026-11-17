module

public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: a recoding's arithmetic, with no ISA in it, for any target's code that runs it (as `Recode.lean`)

/-!
# Sliding-window digits, a bit at a time

A scalar `K` recoded from its lowest bit into digits that are zero or odd and below 16, by an
automaton that reads one bit a step (`step`) and keeps the digits written so far up to date:
with no window in hand (`m = 0`), bit `i` is the digit at `i`, and a set bit opens a window
there (`m = 2`); with a window in hand, opened at `p`, the digit at `i` is zero and the bit,
times the window's weight `m`, is added to the digit at `p`; the window closes after its
fourth bit (`m = 16`). So after `i` bits the digits weighted by powers of two sum to
`K mod 2^i` (`Good.sum`), and after 256 to `K < 2^256` itself (`digits_sum`); each is zero or
odd and below 16 (`digits_odd`), and a nonzero one is followed by three zeros, though nothing
here needs that. `topPos` is the position of the highest digit that is not zero, where a sum
over the digits from the top may start.
-/

@[expose] public section

namespace VG.Proof.Ed25519.Slide

/-- `∑ j < n, u (p + j) 2 ^ j`. -/
def wsum (u : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | p, n + 1 => u p + 2 * wsum u (p + 1) n

theorem wsum_zero (u : Nat → Nat) (p : Nat) : wsum u p 0 = 0 := rfl

theorem wsum_succ (u : Nat → Nat) (p n : Nat) : wsum u p (n + 1) = u p + 2 * wsum u (p + 1) n := rfl

theorem wsum_snoc (u : Nat → Nat) (p n : Nat) : wsum u p (n + 1) = wsum u p n + 2 ^ n * u (p + n) := by
  induction n generalizing p with
  | zero => simp [wsum]
  | succ n ih =>
    rw [wsum_succ, ih, wsum_succ, show p + 1 + n = p + (n + 1) by omega_using [], Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_left_comm (2 ^ n) 2]
    generalize 2 ^ n * u (p + (n + 1)) = e
    omega_arith

theorem wsum_congr {u v : Nat → Nat} {p n : Nat} (h : ∀ j, p ≤ j → j < p + n → u j = v j) :
    wsum u p n = wsum v p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [wsum_succ, wsum_succ, h p (Nat.le_refl _) (by omega_using []),
      ih fun j h1 h2 => h j (by omega_using [h1]) (by omega_using [h2])]

theorem wsum_eq_zero {u : Nat → Nat} {p n : Nat} (h : ∀ j, p ≤ j → j < p + n → u j = 0) : wsum u p n = 0 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [wsum_succ, h p (Nat.le_refl _) (by omega_using []),
      ih fun j h1 h2 => h j (by omega_using [h1]) (by omega_using [h2])]

/-- `u` with `v` at `i`. -/
def upd (u : Nat → Nat) (i v : Nat) (j : Nat) : Nat := if j = i then v else u j

theorem upd_self (u : Nat → Nat) (i v : Nat) : upd u i v i = v := by simp [upd]

theorem upd_ne (u : Nat → Nat) {i j : Nat} (v : Nat) (h : j ≠ i) : upd u i v j = u j := by simp [upd, h]

/-- A digit below `n` raised by `d` raises the sum by `2 ^ p d`. -/
theorem wsum_upd_add (u : Nat → Nat) {p n : Nat} (d : Nat) (hp : p < n) :
    wsum (upd u p (u p + d)) 0 n = wsum u 0 n + 2 ^ p * d := by
  induction n with
  | zero => exact absurd hp (Nat.not_lt_zero _)
  | succ n ih =>
    rw [wsum_snoc, wsum_snoc, Nat.zero_add]
    by_cases h : p = n
    · subst h
      rw [upd_self, wsum_congr (v := u) fun j _ h2 => upd_ne _ _ (by omega_using [h2]), Nat.mul_add, Nat.add_assoc]
    · rw [ih (by omega_using [hp, h]), upd_ne _ _ (fun e => h e.symm)]
      omega_arith

/-- The recoding's state: the bits read, the weight of the next bit in the window in hand (zero
with none), that window's digit so far and its position, and the digits. -/
structure St where
  i : Nat
  m : Nat
  w : Nat
  p : Nat
  u : Nat → Nat

/-- The start: no bit read, no window, no digits. -/
def init : St := ⟨0, 0, 0, 0, fun _ => 0⟩

/-- Bit `i` of `K`. -/
def bit (K i : Nat) : Nat := K / 2 ^ i % 2

theorem bit_lt (K i : Nat) : bit K i < 2 := Nat.mod_lt _ (by decide)

/-- One bit (see the module's description). -/
def step (K : Nat) (s : St) : St :=
  if s.m = 0 then ⟨s.i + 1, 2 * bit K s.i, bit K s.i, s.i, upd s.u s.i (bit K s.i)⟩
  else ⟨s.i + 1, 2 * s.m % 16, s.w + s.m * bit K s.i, s.p,
    upd (upd s.u s.i 0) s.p (s.w + s.m * bit K s.i)⟩

/-- The state after `n` bits. -/
def run (K : Nat) : Nat → St
  | 0 => init
  | n + 1 => step K (run K n)

theorem run_succ (K n : Nat) : run K (n + 1) = step K (run K n) := rfl

/-- The digits of `K < 2 ^ 256`. -/
def digits (K : Nat) : Nat → Nat := (run K 256).u

theorem digits_eq (K q : Nat) : digits K q = (run K 256).u q := rfl

/-- What every state of the recoding satisfies. -/
structure Good (K : Nat) (s : St) : Prop where
  m : s.m = 0 ∨ (s.p < s.i ∧ s.i ≤ s.p + 3 ∧ s.m = 2 ^ (s.i - s.p) ∧ s.u s.p = s.w ∧ s.w < s.m ∧ s.w % 2 = 1)
  w : s.w < 16
  p : s.p ≤ s.i
  above : ∀ q, s.i ≤ q → s.u q = 0
  odd : ∀ q, s.u q = 0 ∨ (s.u q % 2 = 1 ∧ s.u q < 16)
  sum : wsum s.u 0 s.i = K % 2 ^ s.i

theorem init_good (K : Nat) : Good K init :=
  ⟨.inl rfl, by decide, Nat.le_refl _, fun _ _ => rfl, fun _ => .inl rfl, by simp [init, wsum, Nat.mod_one]⟩

/-- The weight is 0, 2, 4 or 8. -/
theorem Good.m_cases {K : Nat} {s : St} (h : Good K s) : s.m = 0 ∨ s.m = 2 ∨ s.m = 4 ∨ s.m = 8 := by
  rcases h.m with h0 | ⟨h1, h2, h3, -⟩
  · exact .inl h0
  · rcases (by omega_using [h1, h2] : s.i - s.p = 1 ∨ s.i - s.p = 2 ∨ s.i - s.p = 3) with e | e | e <;>
      rw [e] at h3 <;> simp [h3]

theorem step_good {K : Nat} {s : St} (h : Good K s) : Good K (step K s) := by
  obtain ⟨i, m, w, p, u⟩ := s
  obtain ⟨hm, hw, hp, habove, hodd, hsum⟩ := h
  dsimp only at hm hw hp habove hodd hsum
  have hb := bit_lt K i
  have hK1 : K % 2 ^ (i + 1) = K % 2 ^ i + 2 ^ i * bit K i := Nat.mod_pow_succ
  unfold step
  dsimp only
  generalize bit K i = b at hb hK1 ⊢
  by_cases h0 : m = 0
  · rw [ite_eq_left h0]
    refine ⟨?_, ?_, ?_, fun q hq => ?_, fun q => ?_, ?_⟩ <;> dsimp only at *
    · rcases (by omega_using [hb] : b = 0 ∨ b = 1) with rfl | rfl
      · exact .inl rfl
      · refine .inr ⟨Nat.lt_succ_self _, by omega_using [], ?_, upd_self _ _ _, by decide, by decide⟩
        rw [Nat.add_sub_cancel_left]
    · omega_using [hb]
    · exact Nat.le_succ _
    · rw [upd_ne _ _ (by omega_using [hq])]
      exact habove q (by omega_using [hq])
    · by_cases hq : q = i
      · rw [hq, upd_self]
        rcases (by omega_using [hb] : b = 0 ∨ b = 1) with rfl | rfl
        · exact .inl rfl
        · exact .inr ⟨by decide, by decide⟩
      · rw [upd_ne _ _ hq]; exact hodd q
    · rw [wsum_snoc, Nat.zero_add, upd_self, wsum_congr (v := u) fun j _ h2 => upd_ne _ _ (by omega_using [h2]),
        hsum, hK1]
  · rw [ite_eq_right h0]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hm.resolve_left h0
    -- The digits after the step, pointwise.
    have hu : ∀ q, upd (upd u i 0) p (w + m * b) q = upd u p (u p + m * b) q := by
      intro q
      by_cases hq : q = p
      · rw [hq, upd_self, upd_self, h4]
      · rw [upd_ne _ _ hq, upd_ne _ _ hq]
        by_cases hqi : q = i
        · rw [hqi, upd_self, habove i (Nat.le_refl _)]
        · rw [upd_ne _ _ hqi]
    have hd : i - p = 1 ∨ i - p = 2 ∨ i - p = 3 := by omega_using [h1, h2]
    have hmc : m = 2 ∨ m = 4 ∨ m = 8 := by
      rcases hd with e | e | e <;> rw [e] at h3 <;> simp [h3]
    have hw' : w + m * b < 2 * m ∧ (w + m * b) % 2 = 1 ∧ w + m * b < 16 := by
      rcases (by omega_using [hb] : b = 0 ∨ b = 1) with rfl | rfl <;> rcases hmc with rfl | rfl | rfl <;>
        omega_using [h5, h6]
    refine ⟨?_, ?_, ?_, fun q hq => ?_, fun q => ?_, ?_⟩ <;> dsimp only at *
    · by_cases h8 : m = 8
      · exact .inl (by rw [h8])
      · have h23 : i - p = 1 ∨ i - p = 2 := by
          rcases hd with e | e | e
          · exact .inl e
          · exact .inr e
          · rw [e] at h3; exact absurd h3 h8
        refine .inr ⟨Nat.lt_succ_of_lt h1, by omega_using [h23], ?_, upd_self _ _ _, ?_, hw'.2.1⟩
        · rcases h23 with e | e
          · rw [show i + 1 - p = 2 by omega_using [e, h1], h3, e]
          · rw [show i + 1 - p = 3 by omega_using [e, h1], h3, e]
        · rcases hmc with e | e | e
          · rw [e] at hw' ⊢; exact hw'.1
          · rw [e] at hw' ⊢; exact hw'.1
          · exact absurd e h8
    · exact hw'.2.2
    · exact Nat.le_succ_of_le hp
    · rw [upd_ne _ _ (by omega_using [hq, h1]), upd_ne _ _ (by omega_using [hq])]
      exact habove q (by omega_using [hq])
    · by_cases hq : q = p
      · rw [hq, upd_self]
        exact .inr ⟨hw'.2.1, hw'.2.2⟩
      · rw [upd_ne _ _ hq]
        by_cases hqi : q = i
        · rw [hqi, upd_self]; exact .inl rfl
        · rw [upd_ne _ _ hqi]; exact hodd q
    · rw [wsum_congr (v := upd u p (u p + m * b)) fun j _ _ => hu j,
        wsum_upd_add _ _ (Nat.lt_succ_of_lt h1), wsum_snoc, Nat.zero_add, habove i (Nat.le_refl _), hsum, hK1,
        h3, ← Nat.mul_assoc, ← Nat.pow_add, show p + (i - p) = i by omega_using [h1]]
      omega_arith

/-- A step with no window in hand. -/
theorem step_idle {K : Nat} {s : St} (h : s.m = 0) :
    (step K s).m = 2 * bit K s.i ∧ (step K s).w = bit K s.i ∧ (step K s).p = s.i ∧
      (step K s).u = upd s.u s.i (bit K s.i) := by
  unfold step
  rw [ite_eq_left h]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A step with a window in hand. -/
theorem step_grow {K : Nat} {s : St} (h : s.m ≠ 0) :
    (step K s).m = 2 * s.m % 16 ∧ (step K s).w = s.w + s.m * bit K s.i ∧ (step K s).p = s.p ∧
      (step K s).u = upd (upd s.u s.i 0) s.p (s.w + s.m * bit K s.i) := by
  unfold step
  rw [ite_eq_right h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem run_good (K : Nat) : ∀ n, Good K (run K n)
  | 0 => init_good K
  | n + 1 => step_good (run_good K n)

theorem step_i (K : Nat) (s : St) : (step K s).i = s.i + 1 := by
  unfold step; split <;> rfl

theorem run_i (K : Nat) : ∀ n, (run K n).i = n
  | 0 => rfl
  | n + 1 => by rw [run_succ, step_i, run_i K n]

/-- The digits sum to `K`. -/
theorem digits_sum {K : Nat} (hK : K < 2 ^ 256) : wsum (digits K) 0 256 = K := by
  have h := (run_good K 256).sum
  rw [run_i, Nat.mod_eq_of_lt hK] at h
  exact h

/-- Each digit is zero, or odd and below 16. -/
theorem digits_odd (K q : Nat) : digits K q = 0 ∨ (digits K q % 2 = 1 ∧ digits K q < 16) :=
  (run_good K 256).odd q

/-! ## The top digit -/

/-- The highest of the positions below `n` whose digit is not zero, or 0 if there is none. -/
def topPos (D : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if D n = 0 then topPos D n else n

theorem topPos_succ_zero {D : Nat → Nat} {n : Nat} (h : D n = 0) : topPos D (n + 1) = topPos D n := by
  rw [topPos, ite_eq_left h]

theorem topPos_succ_ne {D : Nat → Nat} {n : Nat} (h : D n ≠ 0) : topPos D (n + 1) = n := by
  rw [topPos, ite_eq_right h]

theorem topPos_lt (D : Nat → Nat) : ∀ {n : Nat}, 0 < n → topPos D n < n
  | n + 1, _ => by
    by_cases h : D n = 0
    · rw [topPos_succ_zero h]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact Nat.zero_lt_one
      · exact Nat.lt_succ_of_lt (topPos_lt D hn)
    · rw [topPos_succ_ne h]
      exact Nat.lt_succ_self _

/-- The digits above the top one, below `n`, are zero. -/
theorem topPos_zero (D : Nat → Nat) : ∀ (n q : Nat), topPos D n < q → q < n → D q = 0
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, q, h1, h2 => by
    by_cases h : D n = 0
    · rw [topPos_succ_zero h] at h1
      rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with hq | rfl
      · exact topPos_zero D n q h1 hq
      · exact h
    · rw [topPos_succ_ne h] at h1
      omega_using [h1, h2]

end VG.Proof.Ed25519.Slide
