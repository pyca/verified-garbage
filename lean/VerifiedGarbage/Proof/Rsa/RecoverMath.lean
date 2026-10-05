import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Data.Int.ModEq

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.KeyMath`. -/
section

/-!
# RSA keys: the mathematics of the constant-time algorithms

Target-independent models, on naturals, of what the code of
`vg_rsa_crt_values` and `vg_rsa_recover_primes` computes, and their
relation to the specification:

* The binary extended Euclidean algorithm with a fixed number of steps
  (`invIter`), for an odd modulus `m`: from `(a, m, 1, 0)` each step halves
  `u` (after subtracting the smaller of `u` and `v` from the larger if both
  are odd), keeping `x₁ a ≡ u` and `x₂ a ≡ v (mod m)`. `u v` at least halves
  at each step, so after as many steps as `a m` has bits `u = 0`, `v` is
  `gcd(a, m)` and `x₂ a ≡ v` (`invIter_done`): the inverse of `a` modulo `m`
  if `v = 1` (`inverse_eq`), and there is none otherwise (`inverse_none`).
* Bit-serial division with a fixed number of steps (`divIter`): the
  quotient register is shifted into the remainder a bit at a time, and the
  divisor subtracted from the remainder when it does not borrow
  (`divIter_done`).
-/

namespace VG.Proof.Rsa

/-! ## Arithmetic modulo `m` -/

/-- `a - b mod m`, for `a, b < m`: `a - b`, plus `m` if it borrows. -/
def subMod (m a b : Nat) : Nat := if b ≤ a then a - b else a + m - b

/-- `x / 2 mod m` for an odd `m`: `x / 2` if `x` is even, `(x + m) / 2`
if it is odd. -/
def halfMod (m x : Nat) : Nat := if x % 2 = 0 then x / 2 else (x + m) / 2

theorem subMod_lt {m a b : Nat} (ha : a < m) (hb : b < m) : VG.Proof.Rsa.subMod m a b < m := by
  unfold VG.Proof.Rsa.subMod; split <;> omega

theorem subMod_dvd {m a b : Nat} (_ha : a < m) (hb : b < m) :
    (m : Int) ∣ (VG.Proof.Rsa.subMod m a b : Int) - (a - b) := by
  unfold VG.Proof.Rsa.subMod
  split
  · exact ⟨0, by push_cast [Nat.cast_sub (by omega : b ≤ a)]; omega⟩
  · exact ⟨1, by push_cast [Nat.cast_sub (by omega : b ≤ a + m)]; omega⟩

theorem halfMod_lt {m x : Nat} (hm : m % 2 = 1) (hx : x < m) : VG.Proof.Rsa.halfMod m x < m := by
  unfold VG.Proof.Rsa.halfMod; split <;> omega

theorem halfMod_two {m x : Nat} (hm : m % 2 = 1) : 2 * VG.Proof.Rsa.halfMod m x = x ∨ 2 * VG.Proof.Rsa.halfMod m x = x + m := by
  unfold VG.Proof.Rsa.halfMod; split <;> omega

/-- `m` odd divides `z` if it divides `2 z`. -/
theorem dvd_of_dvd_two {m : Nat} {z : Int} (hm : m % 2 = 1) (h : (m : Int) ∣ 2 * z) : (m : Int) ∣ z := by
  have e : z = ((m + 1) / 2 : Nat) * (2 * z) - m * z := by
    have : (((m + 1) / 2 : Nat) : Int) * 2 = m + 1 := by
      have : (m + 1) / 2 * 2 = m + 1 := by omega
      exact_mod_cast this
    rw [← Int.mul_assoc, this]; grind
  rw [e]
  exact Int.dvd_sub (Dvd.dvd.mul_left h _) (Int.dvd_mul_right _ _)

/-! ## The binary extended Euclidean algorithm -/

/-- One step on `(u, v, x₁, x₂)`: if `u` is odd, the larger of `u` and `v`
minus the smaller, as `u`, with `v` the smaller; then `u` halved. `x₁` and
`x₂` follow modulo `m`. -/
def invStep (m : Nat) (st : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  let (u, v, x₁, x₂) := st
  if u % 2 = 1 then
    if u < v then ((v - u) / 2, u, VG.Proof.Rsa.halfMod m (VG.Proof.Rsa.subMod m x₂ x₁), x₁)
    else ((u - v) / 2, v, VG.Proof.Rsa.halfMod m (VG.Proof.Rsa.subMod m x₁ x₂), x₂)
  else (u / 2, v, VG.Proof.Rsa.halfMod m x₁, x₂)

/-- `k` steps. -/
def invIter (m : Nat) : Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat
  | 0, st => st
  | k + 1, st => VG.Proof.Rsa.invStep m (VG.Proof.Rsa.invIter m k st)

/-- The invariant of `invStep` for `a` modulo `m`. -/
structure InvI (a m : Nat) (st : Nat × Nat × Nat × Nat) : Prop where
  v_odd : st.2.1 % 2 = 1
  x₁_lt : st.2.2.1 < m
  x₂_lt : st.2.2.2 < m
  c₁ : (m : Int) ∣ (st.2.2.1 : Int) * a - st.1
  c₂ : (m : Int) ∣ (st.2.2.2 : Int) * a - st.2.1
  g : Nat.gcd st.1 st.2.1 = Nat.gcd a m

theorem gcd_half {u v : Nat} (hu : u % 2 = 0) (hv : v % 2 = 1) : Nat.gcd (u / 2) v = Nat.gcd u v := by
  have hc : Nat.Coprime 2 v := by
    rw [Nat.coprime_comm, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    rw [show v % 2 = 1 from hv]; rfl
  conv_rhs => rw [show u = 2 * (u / 2) by omega]
  exact (Nat.Coprime.gcd_mul_left_cancel _ hc).symm

theorem gcd_sub {u v : Nat} (h : v ≤ u) : Nat.gcd (u - v) v = Nat.gcd u v := by
  rw [Nat.gcd_comm, Nat.gcd_comm u, Nat.gcd_sub_self_right h]

/-- The congruence after halving: `x₁' a ≡ u / 2` from `x₁ a ≡ u`. -/
theorem half_cong {m a x u : Nat} (hm : m % 2 = 1) (hu : u % 2 = 0) (h : (m : Int) ∣ (x : Int) * a - u) :
    (m : Int) ∣ (VG.Proof.Rsa.halfMod m x : Int) * a - (u / 2 : Nat) := by
  apply VG.Proof.Rsa.dvd_of_dvd_two hm
  have e2 : ((u / 2 : Nat) : Int) * 2 = u := by
    have : u / 2 * 2 = u := by omega
    exact_mod_cast this
  rcases VG.Proof.Rsa.halfMod_two (x := x) hm with e | e
  · have : (2 : Int) * ((VG.Proof.Rsa.halfMod m x : Int) * a - (u / 2 : Nat)) = (x : Int) * a - u := by
      have e' : 2 * (VG.Proof.Rsa.halfMod m x : Int) = x := by exact_mod_cast e
      rw [← e2, ← e']; grind
    rw [this]; exact h
  · have : (2 : Int) * ((VG.Proof.Rsa.halfMod m x : Int) * a - (u / 2 : Nat)) = ((x : Int) * a - u) + m * a := by
      have e' : 2 * (VG.Proof.Rsa.halfMod m x : Int) = x + m := by exact_mod_cast e
      rw [← e2]; grind
    rw [this]; exact Int.dvd_add h (Int.dvd_mul_right _ _)

/-- The congruence after a subtraction. -/
theorem sub_cong {m a x₁ x₂ u v : Nat} (hx₁ : x₁ < m) (hx₂ : x₂ < m) (hv : v ≤ u)
    (h₁ : (m : Int) ∣ (x₁ : Int) * a - u) (h₂ : (m : Int) ∣ (x₂ : Int) * a - v) :
    (m : Int) ∣ (VG.Proof.Rsa.subMod m x₁ x₂ : Int) * a - (u - v : Nat) := by
  obtain ⟨c, hc⟩ := VG.Proof.Rsa.subMod_dvd (m := m) hx₁ hx₂
  have : (VG.Proof.Rsa.subMod m x₁ x₂ : Int) * a - (u - v : Nat) = ((x₁ : Int) * a - u) - ((x₂ : Int) * a - v) + m * (c * a) := by
    rw [show (VG.Proof.Rsa.subMod m x₁ x₂ : Int) = (x₁ - x₂) + m * c by omega]
    push_cast [Nat.cast_sub hv]; grind
  rw [this]
  exact Int.dvd_add (Int.dvd_sub h₁ h₂) (Int.dvd_mul_right _ _)

theorem invStep_inv {a m : Nat} (hm : m % 2 = 1) {st : Nat × Nat × Nat × Nat} (h : VG.Proof.Rsa.InvI a m st) :
    VG.Proof.Rsa.InvI a m (VG.Proof.Rsa.invStep m st) := by
  obtain ⟨u, v, x₁, x₂⟩ := st
  obtain ⟨hv, h₁, h₂, c₁, c₂, g⟩ := h
  dsimp only at hv h₁ h₂ c₁ c₂ g
  unfold VG.Proof.Rsa.invStep
  dsimp only
  split
  · rename_i hu
    split
    · rename_i hlt
      refine ⟨hu, VG.Proof.Rsa.halfMod_lt hm (VG.Proof.Rsa.subMod_lt h₂ h₁), h₁, VG.Proof.Rsa.half_cong hm (by omega) (VG.Proof.Rsa.sub_cong h₂ h₁ hlt.le c₂ c₁), c₁, ?_⟩
      dsimp only
      rw [VG.Proof.Rsa.gcd_half (by omega) hu, VG.Proof.Rsa.gcd_sub hlt.le, Nat.gcd_comm, g]
    · rename_i hlt
      refine ⟨hv, VG.Proof.Rsa.halfMod_lt hm (VG.Proof.Rsa.subMod_lt h₁ h₂), h₂, VG.Proof.Rsa.half_cong hm (by omega) (VG.Proof.Rsa.sub_cong h₁ h₂ (by omega) c₁ c₂),
        c₂, ?_⟩
      dsimp only
      rw [VG.Proof.Rsa.gcd_half (by omega) hv, VG.Proof.Rsa.gcd_sub (by omega), g]
  · rename_i hu
    exact ⟨hv, VG.Proof.Rsa.halfMod_lt hm h₁, h₂, VG.Proof.Rsa.half_cong hm (by omega) c₁, c₂, by dsimp only; rw [VG.Proof.Rsa.gcd_half (by omega) hv, g]⟩

/-- `u v` at least halves. -/
theorem invStep_size (m : Nat) (st : Nat × Nat × Nat × Nat) :
    (VG.Proof.Rsa.invStep m st).1 * (VG.Proof.Rsa.invStep m st).2.1 * 2 ≤ st.1 * st.2.1 := by
  obtain ⟨u, v, x₁, x₂⟩ := st
  unfold VG.Proof.Rsa.invStep
  dsimp only
  split
  · split
    · rename_i hlt
      dsimp only
      have : (v - u) / 2 * 2 ≤ v := by omega
      calc (v - u) / 2 * u * 2 = (v - u) / 2 * 2 * u := by grind
        _ ≤ v * u := Nat.mul_le_mul_right _ this
        _ = u * v := Nat.mul_comm _ _
    · dsimp only
      have : (u - v) / 2 * 2 ≤ u := by omega
      calc (u - v) / 2 * v * 2 = (u - v) / 2 * 2 * v := by grind
        _ ≤ u * v := Nat.mul_le_mul_right _ this
  · dsimp only
    have : u / 2 * 2 ≤ u := by omega
    calc u / 2 * v * 2 = u / 2 * 2 * v := by grind
      _ ≤ u * v := Nat.mul_le_mul_right _ this

theorem invIter_inv {a m : Nat} (hm : m % 2 = 1) {st : Nat × Nat × Nat × Nat} (h : VG.Proof.Rsa.InvI a m st) :
    ∀ k, VG.Proof.Rsa.InvI a m (VG.Proof.Rsa.invIter m k st)
  | 0 => h
  | k + 1 => VG.Proof.Rsa.invStep_inv hm (VG.Proof.Rsa.invIter_inv hm h k)

/-- After `k` steps, `u v 2^k` is at most what it was. -/
theorem invIter_size (m : Nat) (st : Nat × Nat × Nat × Nat) : ∀ k,
    (VG.Proof.Rsa.invIter m k st).1 * (VG.Proof.Rsa.invIter m k st).2.1 * 2 ^ k ≤ st.1 * st.2.1
  | 0 => by simp [VG.Proof.Rsa.invIter]
  | k + 1 => by
    have ih := VG.Proof.Rsa.invIter_size m st k
    have hs := VG.Proof.Rsa.invStep_size m (VG.Proof.Rsa.invIter m k st)
    simp only [VG.Proof.Rsa.invIter]
    calc _ = (VG.Proof.Rsa.invStep m (VG.Proof.Rsa.invIter m k st)).1 * (VG.Proof.Rsa.invStep m (VG.Proof.Rsa.invIter m k st)).2.1 * 2 * 2 ^ k := by
            rw [Nat.pow_succ]; grind
      _ ≤ (VG.Proof.Rsa.invIter m k st).1 * (VG.Proof.Rsa.invIter m k st).2.1 * 2 ^ k := Nat.mul_le_mul_right _ hs
      _ ≤ _ := ih

/-- The invariant holds of `(a, m, 1, 0)`. -/
theorem invI_start {a m : Nat} (hm : m % 2 = 1) (h1 : 1 < m) : VG.Proof.Rsa.InvI a m (a, m, 1, 0) :=
  ⟨hm, h1, show 0 < m by omega, ⟨0, by simp⟩, by simp, rfl⟩

/-- After enough steps: `u = 0`, `v = gcd(a, m)`, `x₂ a ≡ v (mod m)` and
`x₂ < m`. -/
theorem invIter_done {a m K : Nat} (hm : m % 2 = 1) (ha : a * m < 2 ^ K) :
    let st := VG.Proof.Rsa.invIter m K (a, m, 1 % m, 0)
    st.1 = 0 ∧ st.2.1 = Nat.gcd a m ∧ (m : Int) ∣ (st.2.2.2 : Int) * a - st.2.1 ∧ st.2.2.2 < m := by
  have h0 : VG.Proof.Rsa.InvI a m (a, m, 1 % m, 0) :=
    ⟨hm, Nat.mod_lt _ (by omega), show 0 < m by omega,
      ⟨((1 % m : Nat) : Int) * a / m - (a / m : Nat), by
        rcases Nat.lt_or_ge m 2 with h | h
        · have : m = 1 := by omega
          subst this; simp
        · rw [Nat.mod_eq_of_lt (by omega)]; simp⟩, by simp, rfl⟩
  have hI := VG.Proof.Rsa.invIter_inv hm h0 K
  have hS := VG.Proof.Rsa.invIter_size m (a, m, 1 % m, 0) K
  dsimp only at hS ⊢
  generalize VG.Proof.Rsa.invIter m K (a, m, 1 % m, 0) = st at hI hS
  obtain ⟨u, v, x₁, x₂⟩ := st
  obtain ⟨hv, -, h₂, -, c₂, g⟩ := hI
  dsimp only at hv h₂ c₂ g hS ⊢
  have hu : u = 0 := by
    rcases Nat.eq_zero_or_pos u with h | h
    · exact h
    · exfalso
      have : 2 ^ K ≤ u * v * 2 ^ K := Nat.le_mul_of_pos_left _ (Nat.mul_pos h (by omega))
      omega
  subst hu
  rw [Nat.gcd_zero_left] at g
  exact ⟨rfl, g, c₂, h₂⟩

/-! ## The inverse of the specification -/

/-- What `Spec.Rsa.xgcd` keeps: `r ≡ s q` and `r' ≡ s' q` modulo `p`, and
the gcd. -/
theorem xgcd_spec (q p : Nat) : ∀ (r : Nat) (s : Int) (r' : Nat) (s' : Int), (p : Int) ∣ s * q - r → (p : Int) ∣ s' * q - r' →
    (p : Int) ∣ (Spec.Rsa.xgcd r s r' s').2 * q - (Spec.Rsa.xgcd r s r' s').1 ∧
      (Spec.Rsa.xgcd r s r' s').1 = Nat.gcd r r' := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro s r' s' h h'
    rw [Spec.Rsa.xgcd]
    split
    · rename_i hr
      subst hr
      exact ⟨h', by rw [Nat.gcd_zero_left]⟩
    · rename_i hr
      have hlt : r' % r < r := Nat.mod_lt _ (by omega)
      have hd : (p : Int) ∣ (s' - (r' / r : Nat) * s) * q - (r' % r : Nat) := by
        have e : (s' - (r' / r : Nat) * s) * q - (r' % r : Nat) = (s' * q - r') - (r' / r : Nat) * (s * q - r) := by
          have := Nat.div_add_mod r' r
          have : ((r' % r : Nat) : Int) = r' - (r' / r : Nat) * r := by
            have h3 : ((r * (r' / r) + r' % r : Nat) : Int) = r' := by exact_mod_cast this
            push_cast at h3; grind
          rw [this]; grind
        rw [e]
        exact Int.dvd_sub h' (Dvd.dvd.mul_left h _)
      obtain ⟨e₁, e₂⟩ := ih _ hlt (s' - (r' / r : Nat) * s) r s hd h
      exact ⟨e₁, by rw [e₂, ← Nat.gcd_rec]⟩

/-- `x q ≡ 1 (mod p)` with `x < p` is the specification's inverse. -/
theorem inverse_eq {q p x : Nat} (hp : 1 < p) (hx : x < p) (h : (p : Int) ∣ (x : Int) * q - 1) :
    Spec.Rsa.inverse q p = some x := by
  -- `gcd(q, p) = 1`.
  have hg : Nat.gcd q p = 1 := by
    obtain ⟨c, hc⟩ := h
    have d1 : ((Nat.gcd q p : Nat) : Int) ∣ (x : Int) * q := Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q p)) _
    have d2 : ((Nat.gcd q p : Nat) : Int) ∣ (p : Int) * c := Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q p)) _
    have : ((Nat.gcd q p : Nat) : Int) ∣ 1 := by
      have := Int.dvd_sub d1 d2
      rwa [show (x : Int) * q - p * c = 1 by omega] at this
    exact Int.natCast_dvd_natCast.mp (by exact_mod_cast this) |> Nat.dvd_one.mp
  obtain ⟨e₁, e₂⟩ := VG.Proof.Rsa.xgcd_spec q p (q % p) 1 p 0
    ⟨(q / p : Nat), by have := Nat.div_add_mod q p
                       have h3 : ((p * (q / p) + q % p : Nat) : Int) = q := by exact_mod_cast this
                       push_cast at h3; omega⟩ (by simp)
  rw [e₂, ← Nat.gcd_rec, Nat.gcd_comm, hg] at e₁
  unfold Spec.Rsa.inverse
  dsimp only
  obtain ⟨s, hs⟩ : ∃ s, (Spec.Rsa.xgcd (q % p) 1 p 0).2 = s := ⟨_, rfl⟩
  rw [hs] at e₁ ⊢
  have hp0 : (0 : Int) < p := by omega
  have hx0 : ((s % (p : Int)).toNat : Int) = s % p := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  -- `x₀ = s mod p` is an inverse too.
  have c0 : (p : Int) ∣ ((s % (p : Int)).toNat : Int) * q - 1 := by
    rw [hx0]
    have : s % p * q - 1 = (s * q - 1) - (p * (s / p)) * q := by
      have := Int.mul_ediv_add_emod s p
      grind
    rw [this]; exact Int.dvd_sub e₁ (Dvd.dvd.mul_right (Int.dvd_mul_right _ _) _)
  generalize (s % (p : Int)).toNat = x₀ at c0 hx0 ⊢
  -- `x₀ = x`: `x ≡ x (x₀ q) = x₀ (x q) ≡ x₀`.
  have hxx : x₀ = x := by
    have d : (p : Int) ∣ (x₀ : Int) - x := by
      have : (x₀ : Int) - x = (x : Int) * ((x₀ : Int) * q - 1) - (x₀ : Int) * ((x : Int) * q - 1) := by grind
      rw [this]; exact Int.dvd_sub (Dvd.dvd.mul_left c0 _) (Dvd.dvd.mul_left h _)
    have hx₀ : x₀ < p := by have := Int.emod_lt_of_pos s hp0; omega
    have := (Nat.modEq_iff_dvd.mpr d)
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx₀, eq_comm] at this
  subst hxx
  have hm : q * x₀ % p = 1 := by
    have : 1 ≡ q * x₀ [MOD p] := by
      rw [Nat.modEq_iff_dvd]
      push_cast
      rw [show (q : Int) * x₀ = x₀ * q by grind]; exact c0
    unfold Nat.ModEq at this
    rw [← this, Nat.mod_eq_of_lt hp]
  exact ite_eq_left_iff.mpr (fun h => absurd hm h)

/-- With `gcd(q, p) ≠ 1`, the specification has no inverse. -/
theorem inverse_none {q p : Nat} (hg : Nat.gcd q p ≠ 1) : Spec.Rsa.inverse q p = none := by
  unfold Spec.Rsa.inverse
  dsimp only
  split
  · rename_i h
    exfalso
    apply hg
    have d1 : Nat.gcd q p ∣ q * ((Spec.Rsa.xgcd (q % p) 1 p 0).2 % (p : Int)).toNat :=
      Nat.dvd_mul_right_of_dvd (Nat.gcd_dvd_left q p) _
    have : Nat.gcd q p ∣ q * ((Spec.Rsa.xgcd (q % p) 1 p 0).2 % (p : Int)).toNat % p :=
      (Nat.dvd_mod_iff (Nat.gcd_dvd_right q p)).mpr d1
    rw [h] at this
    exact Nat.dvd_one.mp this
  · rfl

/-! ## Bit-serial division -/

/-- One step of the division by `D` of the `K`-bit register `Q` into the
remainder `R`: `(R, Q)` shifted left a bit (`Q`'s top bit into `R`), then
`D` subtracted from `R` and `Q`'s new low bit set if it does not borrow. -/
def divStep (D K : Nat) (st : Nat × Nat) : Nat × Nat :=
  let R' := 2 * st.1 + st.2 / 2 ^ (K - 1)
  let Q' := 2 * st.2 % 2 ^ K
  if R' < D then (R', Q') else (R' - D, Q' + 1)

/-- `k` steps. -/
def divIter (D K : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, st => st
  | k + 1, st => VG.Proof.Rsa.divStep D K (VG.Proof.Rsa.divIter D K k st)

/-- One step: the remainder and the quotient of the prefix `x` of the
dividend become those of `2 x + b` for the register's next bit `b`. -/
theorem divStep_inv {D K R Q x q L T P : Nat} (hR : R < D) (hx : R + D * q = x)
    (hQ : Q = L * T + q) (hq : q < T) (hL : L < 2 * P) (hK1 : 2 ^ (K - 1) = T * P) (hK : 2 ^ K = 2 * (T * P))
    (hP : 0 < P) :
    ∃ q', (VG.Proof.Rsa.divStep D K (R, Q)).1 < D ∧ (VG.Proof.Rsa.divStep D K (R, Q)).1 + D * q' = 2 * x + L / P ∧
      (VG.Proof.Rsa.divStep D K (R, Q)).2 = L % P * (2 * T) + q' ∧ q' < 2 * T := by
  have hb : L / P < 2 := by
    rcases Nat.lt_or_ge (L / P) 2 with h | h
    · exact h
    · exfalso; have := Nat.mul_le_mul_right P h; have := Nat.div_mul_le_self L P; omega
  have hLd := Nat.div_add_mod L P
  have hLm := Nat.mod_lt L hP
  generalize L / P = b at hb hLd ⊢
  generalize L % P = L' at hLd hLm ⊢
  have hT : 0 < T := by omega
  -- `Q = b T P + (L' T + q)`, the latter below `T P`.
  have hr : L' * T + q < T * P := by
    have : (L' + 1) * T ≤ P * T := Nat.mul_le_mul_right _ hLm
    rw [Nat.add_mul, Nat.one_mul] at this; rw [Nat.mul_comm T P]; omega
  have eQ : Q = (L' * T + q) + T * P * b := by
    subst hQ; rw [← hLd]; grind
  have hdiv : Q / 2 ^ (K - 1) = b := by
    rw [hK1, eQ, Nat.add_mul_div_left _ _ (Nat.mul_pos hT hP), Nat.div_eq_of_lt hr, Nat.zero_add]
  have hlt2 : L' * (2 * T) + 2 * q < 2 * (T * P) := by
    have : L' * (2 * T) = 2 * (L' * T) := by grind
    omega
  have hmod : 2 * Q % 2 ^ K = L' * (2 * T) + 2 * q := by
    rw [hK, eQ, show 2 * (L' * T + q + T * P * b) = (L' * (2 * T) + 2 * q) + 2 * (T * P) * b by grind,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
  simp only [VG.Proof.Rsa.divStep, hdiv, hmod]
  have e1 : D * (2 * q + 1) = 2 * (D * q) + D := by grind
  have e0 : D * (2 * q) = 2 * (D * q) := by grind
  split
  · exact ⟨2 * q, by assumption, by omega, rfl, by omega⟩
  · exact ⟨2 * q + 1, by omega, by omega, by omega, by omega⟩

theorem divIter_inv {D K N : Nat} (hD : 0 < D) (hN : N < 2 ^ K) :
    ∀ k ≤ K, ∃ q, (VG.Proof.Rsa.divIter D K k (0, N)).1 < D ∧ (VG.Proof.Rsa.divIter D K k (0, N)).1 + D * q = N / 2 ^ (K - k) ∧
      (VG.Proof.Rsa.divIter D K k (0, N)).2 = N % 2 ^ (K - k) * 2 ^ k + q ∧ q < 2 ^ k
  | 0, _ => ⟨0, hD, by simp [VG.Proof.Rsa.divIter, Nat.div_eq_of_lt hN], by simp [VG.Proof.Rsa.divIter, Nat.mod_eq_of_lt hN], by simp⟩
  | k + 1, hk => by
    obtain ⟨q, hR, hx, hQ, hq⟩ := VG.Proof.Rsa.divIter_inv hD hN k (by omega)
    have eP : 2 ^ (K - k) = 2 * 2 ^ (K - (k + 1)) := by
      rw [show K - k = K - (k + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hL : N % 2 ^ (K - k) < 2 * 2 ^ (K - (k + 1)) := eP ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
    have hK1 : 2 ^ (K - 1) = 2 ^ k * 2 ^ (K - (k + 1)) := by rw [← Nat.pow_add]; congr 1; omega
    have hK : 2 ^ K = 2 * (2 ^ k * 2 ^ (K - (k + 1))) := by
      rw [← Nat.pow_add, ← Nat.pow_succ']; congr 1; omega
    obtain ⟨q', h1, h2, h3, h4⟩ := VG.Proof.Rsa.divStep_inv hR hx hQ hq hL hK1 hK (Nat.two_pow_pos _)
    have es : VG.Proof.Rsa.divIter D K (k + 1) (0, N) = VG.Proof.Rsa.divStep D K ((VG.Proof.Rsa.divIter D K k (0, N)).1, (VG.Proof.Rsa.divIter D K k (0, N)).2) := rfl
    rw [es]
    refine ⟨q', h1, ?_, ?_, by rw [Nat.pow_succ]; omega⟩
    · rw [h2]
      -- `N / 2^(K - k - 1) = 2 (N / 2^(K - k)) + (N mod 2^(K - k)) / 2^(K - k - 1)`.
      have e := Nat.div_add_mod N (2 ^ (K - k))
      generalize 2 ^ (K - (k + 1)) = P at eP ⊢
      rw [eP] at e ⊢
      conv_rhs => rw [← e]
      rw [show 2 * P * (N / (2 * P)) + N % (2 * P) = N % (2 * P) + P * (2 * (N / (2 * P))) by grind,
        Nat.add_mul_div_left _ _ (by have := Nat.two_pow_pos (K - k); omega)]
      omega
    · rw [h3, Nat.mod_mod_of_dvd _ (by rw [eP]; exact Nat.dvd_mul_left _ _), Nat.pow_succ]
      grind

/-- After `K` steps from `(0, N)`: the remainder and the quotient. -/
theorem divIter_done {D K N : Nat} (hD : 0 < D) (hN : N < 2 ^ K) : VG.Proof.Rsa.divIter D K K (0, N) = (N % D, N / D) := by
  obtain ⟨q, hR, hx, hQ, hq⟩ := VG.Proof.Rsa.divIter_inv hD hN K (Nat.le_refl _)
  rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hx
  rw [Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.zero_add] at hQ
  have e1 : N % D = (VG.Proof.Rsa.divIter D K K (0, N)).1 := by
    rw [show N % D = ((VG.Proof.Rsa.divIter D K K (0, N)).1 + D * q) % D by rw [hx], Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hR]
  have e2 : N / D = q := by
    rw [show N / D = ((VG.Proof.Rsa.divIter D K K (0, N)).1 + D * q) / D by rw [hx], Nat.add_mul_div_left _ _ hD,
      Nat.div_eq_of_lt hR, Nat.zero_add]
  rw [e1, e2, ← hQ]

end VG.Proof.Rsa

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.RecoverMath`. -/
section

/-!
# Recovering the prime factors: the mathematics

Target-independent models, on naturals, of what the code of
`vg_rsa_recover_primes` computes with a fixed number of steps, and their
relation to the specification (`Spec.Rsa.recoverPrimes`):

* Halvings of `m`, each only if `m` is even, counting them
  (`halveStep`): as many as `m` has bits leave `splitTwos m` (`halve_iter`).
* Squarings under masks (`sqStep`): from `y = g^r mod n`, done if `y = ±1`,
  each live squaring (not done, and fewer than `t`) finds `y` if `y² = 1`,
  stops if `y² = -1` or it is the `t`-th, and continues with `y := y²`
  otherwise; after at least `t` of them, `ok` and `y` are
  `recoverStep`'s result (`sq_result`).
* The candidates `g = 2, 3, …` until one gives a result or 100 are tried
  (`go_found`, `go_none`).
-/

namespace VG.Proof.Rsa

open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries powMod)

/-! ## Halvings -/

/-- `(m, t) ↦ (m / 2, t + 1)` if `m` is even. -/
def halveStep (st : Nat × Nat) : Nat × Nat := if st.1 % 2 = 0 then (st.1 / 2, st.2 + 1) else st

theorem splitTwos_odd {m : Nat} (h : m % 2 = 1) : splitTwos m = (0, m) := by
  rw [Spec.Rsa.splitTwos.eq_1]; simp [h]

theorem splitTwos_even {m : Nat} (h0 : m ≠ 0) (h : m % 2 = 0) :
    splitTwos m = ((splitTwos (m / 2)).1 + 1, (splitTwos (m / 2)).2) := by
  have h' : ¬ (m = 0 ∨ m % 2 = 1) := by omega
  rw [Spec.Rsa.splitTwos.eq_1]; simp only [h', ite_false]

/-- `m = 2^t r` with `r` odd. -/
theorem splitTwos_spec {m : Nat} (hm : 0 < m) :
    m = 2 ^ (splitTwos m).1 * (splitTwos m).2 ∧ (splitTwos m).2 % 2 = 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · obtain ⟨e1, e2⟩ := ih (m / 2) (by omega) (by omega)
      rw [VG.Proof.Rsa.splitTwos_even (by omega) h]
      refine ⟨?_, e2⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ _) 2, Nat.mul_assoc, ← e1]
      omega
    · rw [VG.Proof.Rsa.splitTwos_odd h]
      exact ⟨by simp, h⟩

theorem splitTwos_lt {m K : Nat} (hm : 0 < m) (hK : m < 2 ^ K) : (splitTwos m).1 < K := by
  obtain ⟨e1, e2⟩ := VG.Proof.Rsa.splitTwos_spec hm
  have h1 : 2 ^ (splitTwos m).1 ≤ m :=
    calc 2 ^ (splitTwos m).1 ≤ 2 ^ (splitTwos m).1 * (splitTwos m).2 := Nat.le_mul_of_pos_right _ (by omega)
      _ = m := e1.symm
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_le_of_lt h1 hK)

/-- At least `t` halvings of `m = 2^t r` leave `(r, s + t)`. -/
theorem halve_iter {m : Nat} (hm : 0 < m) {K : Nat} (hK : (splitTwos m).1 ≤ K) (s : Nat) :
    VG.Proof.Rsa.halveStep^[K] (m, s) = ((splitTwos m).2, s + (splitTwos m).1) := by
  induction K generalizing m s with
  | zero =>
    have h0 : (splitTwos m).1 = 0 := by omega
    have hodd : m % 2 = 1 := by
      have := (VG.Proof.Rsa.splitTwos_spec hm).1; rw [h0, Nat.pow_zero, Nat.one_mul] at this
      have := (VG.Proof.Rsa.splitTwos_spec hm).2; omega
    rw [VG.Proof.Rsa.splitTwos_odd hodd]; rfl
  | succ K ih =>
    rw [Function.iterate_succ_apply]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have e := VG.Proof.Rsa.splitTwos_even (by omega) h
      have hs : VG.Proof.Rsa.halveStep (m, s) = (m / 2, s + 1) := by simp [VG.Proof.Rsa.halveStep, h]
      rw [hs, ih (by omega) (by rw [e] at hK; dsimp only at hK; omega), e]
      simp only [Prod.mk.injEq, true_and]
      omega
    · have hs : VG.Proof.Rsa.halveStep (m, s) = (m, s) := by simp [VG.Proof.Rsa.halveStep, h]
      rw [hs, ih hm (by rw [VG.Proof.Rsa.splitTwos_odd h]; exact Nat.zero_le _), VG.Proof.Rsa.splitTwos_odd h]

/-- `K` halvings of `0 < m < 2^K`, from `t = 0`: `splitTwos m`, swapped. -/
theorem halve_done {m K : Nat} (hm : 0 < m) (hK : m < 2 ^ K) :
    VG.Proof.Rsa.halveStep^[K] (m, 0) = ((splitTwos m).2, (splitTwos m).1) := by
  rw [VG.Proof.Rsa.halve_iter hm (Nat.le_of_lt (VG.Proof.Rsa.splitTwos_lt hm hK)), Nat.zero_add]

/-! ## Squarings -/

/-- A squaring under masks, the `k`-th (from 0) of a candidate whose `m`
has `t` factors 2: `(y, done, ok)`. -/
def sqStep (n t k : Nat) (st : Nat × Bool × Bool) : Nat × Bool × Bool :=
  let x := st.1 * st.1 % n
  let live := !st.2.1 && decide (k < t)
  let e1 := decide (x = 1)
  let stop := decide (x = n - 1) || decide (k + 1 = t)
  (if live && !e1 && !stop then x else st.1, st.2.1 || (live && (e1 || stop)), st.2.2 || (live && e1))

/-- The first `k` squarings. -/
def sqIter (n t : Nat) : Nat → Nat × Bool × Bool → Nat × Bool × Bool
  | 0, st => st
  | k + 1, st => VG.Proof.Rsa.sqStep n t k (VG.Proof.Rsa.sqIter n t k st)

/-- The result of a state: `y` if `ok`. -/
def sqRes (st : Nat × Bool × Bool) : Option Nat := if st.2.2 then some st.1 else none

theorem sqStep_done {n t k : Nat} {y : Nat} {ok : Bool} : VG.Proof.Rsa.sqStep n t k (y, true, ok) = (y, true, ok) := by
  simp [VG.Proof.Rsa.sqStep]

theorem sqStep_late {n t k : Nat} (hk : t ≤ k) (st : Nat × Bool × Bool) : VG.Proof.Rsa.sqStep n t k st = st := by
  have : decide (k < t) = false := by simp; omega
  simp [VG.Proof.Rsa.sqStep, this]

/-- A live squaring: done with `squarings 0`'s result if it is the last,
and otherwise with `squarings (j + 1)`'s, or not done and `squarings j`
of the new `y`. -/
theorem sqStep_live {n t k y : Nat} (hk : k < t) :
    let st := VG.Proof.Rsa.sqStep n t k (y, false, false)
    (st.2.1 = true → VG.Proof.Rsa.sqRes st = recoverStep.squarings n (t - 1 - k) y) ∧
    (st.2.1 = false → st.2.2 = false ∧ k + 1 < t ∧
      recoverStep.squarings n (t - 1 - k) y = recoverStep.squarings n (t - 1 - (k + 1)) st.1) := by
  intro st
  have hl : (!false && decide (k < t)) = true := by simp [hk]
  rcases Nat.lt_or_ge (k + 1) t with h1 | h1
  · -- Not the last.
    obtain ⟨j, hj⟩ : ∃ j, t - 1 - k = j + 1 := ⟨t - 1 - k - 1, by omega⟩
    have hj' : t - 1 - (k + 1) = j := by omega
    have hlast : decide (k + 1 = t) = false := by simp; omega
    rw [hj, hj']
    simp only [st, VG.Proof.Rsa.sqStep, hl, hlast, Bool.or_false, recoverStep.squarings, Bool.true_and, Bool.false_or]
    by_cases e1 : y * y % n = 1
    · simp [e1, VG.Proof.Rsa.sqRes]
    · by_cases e2 : y * y % n = n - 1
      · simp [e2, VG.Proof.Rsa.sqRes]
      · simp [e1, e2, h1]
  · -- The last.
    have hj : t - 1 - k = 0 := by omega
    have hlast : decide (k + 1 = t) = true := by simp; omega
    rw [hj]
    simp only [st, VG.Proof.Rsa.sqStep, hl, hlast, Bool.or_true, recoverStep.squarings, Bool.true_and, Bool.false_or]
    by_cases e1 : y * y % n = 1
    · simp [e1, VG.Proof.Rsa.sqRes]
    · simp [e1, VG.Proof.Rsa.sqRes]

/-- What holds after `k ≤ t` squarings, for the overall result `R`. -/
def SqInv (n t : Nat) (R : Option Nat) (k : Nat) (st : Nat × Bool × Bool) : Prop :=
  (st.2.1 = true → VG.Proof.Rsa.sqRes st = R) ∧ (st.2.1 = false → st.2.2 = false ∧ k < t ∧
    R = recoverStep.squarings n (t - 1 - k) st.1)

theorem sqInv_step {n t : Nat} {R : Option Nat} {k : Nat} {st : Nat × Bool × Bool} (h : VG.Proof.Rsa.SqInv n t R k st) :
    VG.Proof.Rsa.SqInv n t R (k + 1) (VG.Proof.Rsa.sqStep n t k st) := by
  rcases st with ⟨y, done, ok⟩
  cases done
  · obtain ⟨hok, hk, hR⟩ := h.2 rfl
    dsimp only at hok
    subst hok
    obtain ⟨a, b⟩ := VG.Proof.Rsa.sqStep_live (n := n) (y := y) hk
    exact ⟨fun hd => (a hd).trans hR.symm, fun hd => by
      obtain ⟨c, d, e⟩ := b hd
      exact ⟨c, d, hR.trans e⟩⟩
  · rw [VG.Proof.Rsa.sqStep_done]
    exact ⟨h.1, fun h' => by simp at h'⟩

/-- `recoverStep`, from `y = g^r mod n`: `done` if `y = ±1`, and otherwise
`squarings (t - 1) y`. -/
theorem recoverStep_eq (n t r g : Nat) :
    recoverStep n t r g = if powMod g r n = 1 ∨ powMod g r n = n - 1 then none
      else recoverStep.squarings n (t - 1) (powMod g r n) := rfl

/-- The start of the squarings. -/
def sqStart (n y : Nat) : Nat × Bool × Bool := (y, decide (y = 1) || decide (y = n - 1), false)

/-- At least `t ≥ 1` squarings: `recoverStep`'s result. -/
theorem sq_result {n t r g K : Nat} (ht : 1 ≤ t) (hK : t ≤ K) :
    VG.Proof.Rsa.sqRes (VG.Proof.Rsa.sqIter n t K (VG.Proof.Rsa.sqStart n (powMod g r n))) = recoverStep n t r g := by
  have h0 : VG.Proof.Rsa.SqInv n t (recoverStep n t r g) 0 (VG.Proof.Rsa.sqStart n (powMod g r n)) := by
    rw [VG.Proof.Rsa.recoverStep_eq]
    by_cases hy : powMod g r n = 1 ∨ powMod g r n = n - 1
    · have hd : (VG.Proof.Rsa.sqStart n (powMod g r n)).2.1 = true := by simpa [VG.Proof.Rsa.sqStart] using hy
      refine ⟨fun _ => ?_, fun h => by rw [hd] at h; cases h⟩
      simp only [hy, ite_true]; rfl
    · have hd : (VG.Proof.Rsa.sqStart n (powMod g r n)).2.1 = false := by simpa [VG.Proof.Rsa.sqStart] using hy
      refine ⟨fun h => (by rw [hd] at h; cases h), fun _ => ⟨rfl, by omega, ?_⟩⟩
      simp only [hy, ite_false, Nat.sub_zero]; rfl
  -- The invariant up to `t`.
  have hI : ∀ k ≤ t, VG.Proof.Rsa.SqInv n t (recoverStep n t r g) k (VG.Proof.Rsa.sqIter n t k (VG.Proof.Rsa.sqStart n (powMod g r n))) := by
    intro k hk
    induction k with
    | zero => exact h0
    | succ k ih => exact VG.Proof.Rsa.sqInv_step (ih (by omega))
  -- Done after `t`.
  have hd : (VG.Proof.Rsa.sqIter n t t (VG.Proof.Rsa.sqStart n (powMod g r n))).2.1 = true := by
    by_contra hnd
    have := (hI t (Nat.le_refl _)).2 (by simpa using hnd)
    omega
  -- Nothing changes after `t`.
  have hlate : ∀ j, VG.Proof.Rsa.sqIter n t (t + j) (VG.Proof.Rsa.sqStart n (powMod g r n)) = VG.Proof.Rsa.sqIter n t t (VG.Proof.Rsa.sqStart n (powMod g r n)) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← Nat.add_assoc, VG.Proof.Rsa.sqIter, ih, VG.Proof.Rsa.sqStep_late (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, K = t + j := ⟨K - t, by omega⟩
  rw [hlate]
  exact (hI t (Nat.le_refl _)).1 hd

/-- The `y` that `squarings` finds has `y² ≡ 1`. -/
theorem squarings_some {n : Nat} : ∀ {j x y : Nat}, recoverStep.squarings n j x = some y → y * y % n = 1
  | 0, x, y, h => by
    simp only [recoverStep.squarings] at h
    split at h
    · cases h; assumption
    · cases h
  | j + 1, x, y, h => by
    simp only [recoverStep.squarings] at h
    split at h
    · cases h; assumption
    · split at h
      · cases h
      · exact VG.Proof.Rsa.squarings_some h

/-- The `y` that `recoverStep` finds has `y² ≡ 1`. -/
theorem recoverStep_some {n t r g y : Nat} (h : recoverStep n t r g = some y) : y * y % n = 1 := by
  rw [VG.Proof.Rsa.recoverStep_eq] at h
  split at h
  · cases h
  · exact VG.Proof.Rsa.squarings_some h

/-! ## The candidates -/

/-- `recoverPrimes.go` from candidate `c` (`g = c + 2`), all those before
having failed. -/
theorem go_eq (n t r : Nat) {c : Nat} (hc : c < recoverTries) :
    recoverPrimes.go n t r (recoverTries - c) =
      match recoverStep n t r (c + 2) with
      | some y => (some (max (Nat.gcd (y - 1) n) (n / Nat.gcd (y - 1) n),
          min (Nat.gcd (y - 1) n) (n / Nat.gcd (y - 1) n)), c + 1)
      | none => recoverPrimes.go n t r (recoverTries - (c + 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, recoverTries - c = k + 1 := ⟨recoverTries - c - 1, by omega⟩
  have e1 : recoverTries - k = c + 1 := by omega
  have e2 : recoverTries - (c + 1) = k := by omega
  rw [hk, e2, recoverPrimes.go, e1]
  rfl

theorem go_last (n t r : Nat) : recoverPrimes.go n t r (recoverTries - recoverTries) = (none, recoverTries) := by
  rw [Nat.sub_self, recoverPrimes.go]

/-- `recoverPrimes` when step 1 fails. -/
theorem recoverPrimes_none {n e d : Nat} (h : d * e < 2 ∨ (d * e - 1) % 2 = 1) : recoverPrimes n e d = (none, 0) := by
  simp only [recoverPrimes, h, ite_true]

/-- `recoverPrimes` when step 1 passes: the candidates from `splitTwos (d e - 1)`. -/
theorem recoverPrimes_go {n e d : Nat} (h : ¬(d * e < 2 ∨ (d * e - 1) % 2 = 1)) :
    recoverPrimes n e d =
      recoverPrimes.go n (splitTwos (d * e - 1)).1 (splitTwos (d * e - 1)).2 recoverTries := by
  simp only [recoverPrimes, h, ite_false]

/-- `recoverPrimes.go` tries at least one candidate. -/
theorem go_pos (n t r : Nat) : ∀ k, k ≤ recoverTries → 1 ≤ (recoverPrimes.go n t r k).2
  | 0, _ => by rw [recoverPrimes.go]; decide
  | k + 1, hk => by
    rw [recoverPrimes.go]
    split
    · show 1 ≤ recoverTries - k
      unfold recoverTries at *; omega
    · exact VG.Proof.Rsa.go_pos n t r k (by omega)

end VG.Proof.Rsa

end
