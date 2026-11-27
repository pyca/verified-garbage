module

public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA: `Decompose` and `Power2Round` by multiplications and shifts, for every target

The rounding functions of FIPS 204 §7.4 in the form an implementation computes
them, for every coefficient `a < q`:

* `Power2Round(a)` is `(⌊(a + 4095) / 2¹³⌋, ((a + 4095) mod 2¹³) - 4095)`
  (`power2Round_eq`);
* `Decompose(a)`, for `γ₂` in `gamma2s`: its `r₁` is `f mod m`, for
  `f = ⌊(a + γ₂ - 1) / (2γ₂)⌋` (`hbF`, at most `m`) and `m = (q - 1)/(2γ₂)`
  (`hbM`: 16 or 44); its `r₀` is `a - r₁ · 2γ₂`, but `a - q` when `f = m`
  (`decompose_eq`);
* `f` without a division (`hbF_eq`), as the reference implementation
  computes it: `b = ⌊(a + 127)/2⁷⌋`, then `⌊(1025 b + 2²¹)/2²²⌋` for
  `γ₂ = (q - 1)/32` and `⌊(11275 b + 2²³)/2²⁴⌋` for `γ₂ = (q - 1)/88`
  (`hbMul`, `hbAdd`, `hbShift`). `omega` proves it for every `a < q`, for
  both values of `γ₂`, without enumerating `a`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Round

open VG.Spec.MlDsa

theorem q_eq : q = 8380417 := rfl

theorem mem_gamma2s {γ₂ : Nat} (h : γ₂ ∈ gamma2s) : γ₂ = 95232 ∨ γ₂ = 261888 := by
  simpa [gamma2s] using h

/-! ## `Decompose` -/

/-- `m = (q - 1)/(2γ₂)`, the number of values of `r₁`. -/
def hbM (γ₂ : Nat) : Nat := (q - 1) / (2 * γ₂)

/-- `⌊(a + γ₂ - 1)/(2γ₂)⌋`: `r₁` of `Decompose(a)` before it is reduced modulo `m`. -/
def hbF (γ₂ a : Nat) : Nat := (a + γ₂ - 1) / (2 * γ₂)

theorem hbM_32 : hbM 261888 = 16 := rfl
theorem hbM_88 : hbM 95232 = 44 := rfl

theorem hbF_le {γ₂ : Nat} (h : γ₂ ∈ gamma2s) {a : Nat} (ha : a < q) : hbF γ₂ a ≤ hbM γ₂ := by
  rcases mem_gamma2s h with rfl | rfl <;> simp only [hbF, hbM, q_eq] at * <;> omega_arith

theorem hbM_mul {γ₂ : Nat} (h : γ₂ ∈ gamma2s) : hbM γ₂ * (2 * γ₂) = q - 1 := by
  rcases mem_gamma2s h with rfl | rfl <;> rfl

/-- `a mod± 2γ₂`, from `a` as a multiple of `2γ₂` and a remainder in `(-γ₂, γ₂]`. -/
theorem modPm_of {a e f : Int} {g : Nat} (h : a = e + ((2 * g : Nat) : Int) * f) (h₁ : -(g : Int) < e)
    (h₂ : e ≤ g) : modPm a (2 * g) = e := by
  simp only [modPm, h, Int.add_mul_emod_self_left, Nat.mul_div_cancel_left g (show 0 < 2 by decide)]
  rcases Int.lt_or_le e 0 with hn | hn
  · rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega_using [h₁]) (by omega_using [hn]),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega_using [h₁])), Int.add_sub_cancel]
  · rw [Int.emod_eq_of_lt hn (by omega_using [h₁, h₂]),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [h₂]))]

/-- `Decompose(a)`: `(f mod m, a - (f mod m) · 2γ₂)`, less `q` when `f = m`. -/
theorem decompose_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    decompose γ₂ r = (((hbF γ₂ r.val % hbM γ₂ : Nat) : Int),
      (r.val : Int) - ((hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) : Nat) : Int) -
        (if hbF γ₂ r.val = hbM γ₂ then (q : Int) else 0)) := by
  have hf := hbF_le h r.isLt
  have hm := hbM_mul h
  have hg : 0 < γ₂ := by rcases mem_gamma2s h with rfl | rfl <;> decide
  -- `a + γ₂ - 1 = 2γ₂ f + s`
  have hd : 2 * γ₂ * hbF γ₂ r.val + (r.val + γ₂ - 1) % (2 * γ₂) = r.val + γ₂ - 1 := Nat.div_add_mod _ _
  have hs : (r.val + γ₂ - 1) % (2 * γ₂) < 2 * γ₂ := Nat.mod_lt _ (by omega_using [hg])
  simp only [decompose]
  generalize (r.val + γ₂ - 1) % (2 * γ₂) = s at hd hs
  generalize hbF γ₂ r.val = f at *
  generalize r.val = a at *
  generalize hbM γ₂ = m at *
  rw [Nat.mul_comm] at hd
  have he : modPm a (2 * γ₂) = (a : Int) - ((f * (2 * γ₂) : Nat) : Int) := by
    refine modPm_of (f := f) ?_ (by omega_using [hd, hs, hg]) (by omega_using [hd, hs, hg])
    rw [← Int.natCast_mul, Nat.mul_comm f, Int.sub_add_cancel]
  rw [he]
  have hq : ((q - 1 : Nat) : Int) = (q : Int) - 1 := rfl
  rw [Int.sub_sub_self, ← hq, ← hm]
  by_cases hc : f = m
  · subst hc
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true rfl), Nat.mod_self,
      Nat.zero_mul, hm, hq]
    refine Prod.ext rfl ?_
    show (a : Int) - ((q : Int) - 1) - 1 = a - ((0 : Nat) : Int) - q
    omega_using []
  · have hlt : f < m := by omega_using [hf, hc]
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun e => hc (Nat.eq_of_mul_eq_mul_right (by omega_using [hg]) (Int.natCast_inj.mp e))),
      ite_eq_right_of_eq_false _ _ (eq_false hc), Nat.mod_eq_of_lt hlt, ← Int.natCast_ediv,
      Nat.mul_div_cancel _ (by omega_using [hg]), Int.sub_zero]

theorem highBits_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    highBits γ₂ r = ((hbF γ₂ r.val % hbM γ₂ : Nat) : Int) := by
  rw [highBits, decompose_eq h]

theorem lowBits_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    lowBits γ₂ r = (r.val : Int) - ((hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) : Nat) : Int) -
      (if hbF γ₂ r.val = hbM γ₂ then (q : Int) else 0) := by
  rw [lowBits, decompose_eq h]

/-! ## `f` by a multiplication and shifts -/

/-- The multiplier. -/
def hbMul (γ₂ : Nat) : Nat := if γ₂ = 261888 then 1025 else 11275

/-- The shift. -/
def hbShift (γ₂ : Nat) : Nat := if γ₂ = 261888 then 22 else 24

/-- Half of `2 ^ hbShift`, which rounds the quotient. -/
def hbAdd (γ₂ : Nat) : Nat := if γ₂ = 261888 then 2 ^ 21 else 2 ^ 23

/-- `f` as the reference implementation computes it. -/
theorem hbF_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) {a : Nat} (ha : a < q) :
    hbF γ₂ a = ((a + 127) / 128 * hbMul γ₂ + hbAdd γ₂) / 2 ^ hbShift γ₂ := by
  rw [q_eq] at ha
  rcases mem_gamma2s h with rfl | rfl
  · show (a + 95232 - 1) / (2 * 95232) = ((a + 127) / 128 * 11275 + 2 ^ 23) / 2 ^ 24
    omega_arith
  · show (a + 261888 - 1) / (2 * 261888) = ((a + 127) / 128 * 1025 + 2 ^ 21) / 2 ^ 22
    omega_arith

/-! ## `ℤ_q` -/

theorem ofInt_val (x : Int) : (ofInt x).val = (x % (q : Int)).toNat % q := rfl

/-- `ofInt (a - x)` for `x ≤ q`, as a conditional addition of `q` computes it. -/
theorem ofInt_sub_val {a x : Nat} (ha : a < q) (hx : x ≤ q) (c : Int) :
    (ofInt ((a : Int) - (x : Int) - c * (q : Int))).val = if a < x then a + q - x else a - x := by
  rw [ofInt_val, q_eq] at *
  split <;> omega_arith

theorem val_add (a b : Zq) : (a + b).val = (a.val + b.val) % q := Fin.val_add a b

/-! ## `LowBits` -/

/-- `LowBits(a)` modulo `q`: `a - r₁ · 2γ₂` plus `q` if it is negative. -/
theorem lowBits_val {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (r : Zq) :
    (ofInt (lowBits γ₂ r)).val =
      if r.val < hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) then r.val + q - hbF γ₂ r.val % hbM γ₂ * (2 * γ₂)
      else r.val - hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) := by
  have hx : hbF γ₂ r.val % hbM γ₂ * (2 * γ₂) ≤ q := by
    have := hbM_mul h
    have : hbF γ₂ r.val % hbM γ₂ < hbM γ₂ := Nat.mod_lt _ (by rcases mem_gamma2s h with rfl | rfl <;> decide)
    have := Nat.mul_le_mul_right (2 * γ₂) (Nat.le_of_lt this)
    omega_arith
  rw [lowBits_eq h, ← ofInt_sub_val r.isLt hx (if hbF γ₂ r.val = hbM γ₂ then 1 else 0)]
  congr 2
  split <;> simp

/-! ## `Power2Round` -/

theorem power2Round_eq (r : Zq) :
    power2Round r = ((((r.val + 4095) / 8192 : Nat) : Int), (((r.val + 4095) % 8192 : Nat) : Int) - 4095) := by
  have := r.isLt
  simp only [power2Round, modPm, d, q_eq] at *
  split <;> simp only [Prod.mk.injEq] <;> omega_arith

theorem power2Round_t0 (r : Zq) :
    (ofInt (power2Round r).2).val =
      if (r.val + 4095) % 8192 < 4095 then (r.val + 4095) % 8192 + q - 4095 else (r.val + 4095) % 8192 - 4095 := by
  rw [power2Round_eq]
  have := ofInt_sub_val (a := (r.val + 4095) % 8192) (x := 4095)
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)) (by decide) 0
  rw [← this, Int.zero_mul, Int.sub_zero]
  rfl

/-! ## `UseHint` and `MakeHint` -/

/-- `UseHint(h, a)`: `(f + m + δ) mod m` for `δ` 0 if not `h`, and else 1 if
`r₀ > 0`, that is `f · 2γ₂ < a`, and -1 otherwise. -/
theorem useHint_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (b : Bool) (r : Zq) :
    useHint γ₂ b r = (((if b then (if hbF γ₂ r.val * (2 * γ₂) < r.val then hbF γ₂ r.val + hbM γ₂ + 1
      else hbF γ₂ r.val + hbM γ₂ - 1) else hbF γ₂ r.val + hbM γ₂) % hbM γ₂ : Nat) : Int) := by
  have hr := r.isLt
  have hf := hbF_le h hr
  have hm := hbM_mul h
  have m0 : 0 < hbM γ₂ := by rcases mem_gamma2s h with rfl | rfl <;> decide
  unfold useHint
  rw [decompose_eq h]
  dsimp only
  rw [show (q - 1) / (2 * γ₂) = hbM γ₂ from rfl]
  generalize r.val = a at *
  generalize hbF γ₂ a = f at *
  generalize hbM γ₂ = m at *
  cases b
  · simp only [Bool.false_eq_true, false_and, ↓reduceIte, Nat.add_mod_right]
  simp only [true_and, ↓reduceIte]
  by_cases hc : f = m
  · subst hc
    rw [Nat.mod_self, Nat.zero_mul, hm]
    simp only [↓reduceIte]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [hr])), ite_eq_left_of_eq_true _ _ (eq_true (by omega_using [hr])),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [hr])), Nat.add_sub_assoc m0, Nat.add_mod_left,
      Int.natCast_emod, ← Int.add_emod_right]
    exact congrArg (· % (f : Int)) (by omega_using [m0])
  · have hlt : f < m := by omega_using [hf, hc]
    rw [Nat.mod_eq_of_lt hlt, ite_eq_right_of_eq_false _ _ (eq_false hc), Int.sub_zero]
    by_cases hp : f * (2 * γ₂) < a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_using [hp])), ite_eq_left_of_eq_true _ _ (eq_true hp),
        Nat.add_right_comm, Nat.add_mod_right, Int.natCast_emod]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [hp])), ite_eq_left_of_eq_true _ _ (eq_true (by omega_using [hp])),
        ite_eq_right_of_eq_false _ _ (eq_false hp), Int.natCast_emod, ← Int.add_emod_right]
      exact congrArg (· % (m : Int)) (by omega_using [m0])

/-- `MakeHint(z, r)`: whether the `f mod m` of `r` and of `r + z` differ. -/
theorem makeHint_eq {γ₂ : Nat} (h : γ₂ ∈ gamma2s) (z r : Zq) :
    makeHint γ₂ z r = decide (hbF γ₂ r.val % hbM γ₂ ≠ hbF γ₂ ((r.val + z.val) % q) % hbM γ₂) := by
  unfold makeHint
  rw [highBits_eq h, highBits_eq h, val_add]
  simp only [ne_eq, Int.natCast_inj]

/-! ## Norms -/

/-- `‖a‖∞ < B` for `a ∈ ℤ_q`: `a < B` or `q - a < B`. -/
theorem normZq_lt (a : Zq) (B : Nat) : normZq a < B ↔ a.val < B ∨ q - a.val < B := by
  have := a.isLt
  simp only [normZq, modPm, q_eq] at *
  split <;> omega_arith

theorem foldl_max_lt (L : List Nat) (a B : Nat) : L.foldl max a < B ↔ a < B ∧ ∀ x ∈ L, x < B := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih, Nat.max_lt]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

/-- `‖f‖∞ < B` for `f ∈ R_q`: each coefficient's is. -/
theorem normRq_lt (f : Poly) (B : Nat) : normRq [f] < B ↔ ∀ i < n, normZq f[i]! < B := by
  simp only [normRq, List.flatMap_cons, List.flatMap_nil, List.append_nil, foldl_max_lt,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Vector.mem_toList_iff]
  constructor
  · intro ⟨_, h⟩ i hi
    rw [getElem!_pos f i hi]
    exact h _ (Vector.getElem_mem hi)
  · intro h
    refine ⟨?_, fun x hx => ?_⟩
    · have := h 0 (by decide); omega_arith
    · obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hx
      have := h i hi
      rwa [getElem!_pos f i hi] at this

end VG.Proof.MlDsa.Round
