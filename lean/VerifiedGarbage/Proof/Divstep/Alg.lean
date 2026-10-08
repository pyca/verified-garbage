import VerifiedGarbage.Proof.Divstep.State
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Word

/-!
# Inversion by batches of divsteps

The inverse of `x` modulo an odd `p` (`0 ≤ x < p`), as the code computes it
(`invRun`): from `(d, f, g) = (1, p, x)` and coefficients `(a, b) = (0, 1)`,
each batch takes the matrix `(u, v, q, r)` of `N` divsteps, replaces
`(f, g)` by `(u f + v g, q f + r g) / 2^N` (exactly: `batch_dfg`), and
`(a, b)` by `(u a + v b, q a + r b) / 2^64 mod p` (`mred`, adding the multiple
of `p` that clears the low word, then at most one `p` back into `[0, p)`).
With `f ≡ x a 2^(c i)` and `g ≡ x b 2^(c i)` modulo `p`, `c = 64 - N`
(`invRun_inv`), once `g = 0`, `f = ±gcd(p, x) = ±1`, and
`x (± a) 2^(c i) ≡ 1` (`invRun_spec`).
-/

namespace VG.Proof.Divstep

/-- `t / 2^64 mod p`: `t` plus the multiple `k p` (`k = t m mod 2^64`, for
`m = -p⁻¹ mod 2^64`) that clears its low word, over `2^64`. -/
def mredRaw (p m t : Int) : Int := (t + (t * m) % 2 ^ 64 * p) / 2 ^ 64

/-- Into `[0, p)` from `(-p, 2p)`. -/
def norm (p t : Int) : Int := if t < 0 then t + p else if p ≤ t then t - p else t

def mred (p m t : Int) : Int := norm p (mredRaw p m t)

/-- A batch of `N` divsteps. -/
def batch (N : Nat) (p m : Int) (s : IState) : IState :=
  let t := msteps N (MSt.init s.d s.f s.g)
  ⟨t.d, (t.u * s.f + t.v * s.g) / 2 ^ N, (t.q * s.f + t.r * s.g) / 2 ^ N,
    mred p m (t.u * s.a + t.v * s.b), mred p m (t.q * s.a + t.r * s.b)⟩

/-- `B` batches from the start. -/
def invRun (N : Nat) (p m x : Int) : Nat → IState
  | 0 => ⟨1, p, x, 0, 1⟩
  | B + 1 => batch N p m (invRun N p m x B)

/-- A batch's `(d, f, g)` are `N` divsteps'. -/
theorem batch_dfg {N : Nat} {p m : Int} {s : IState} (hf : s.f % 2 = 1) :
    ((batch N p m s).d, (batch N p m s).f, (batch N p m s).g) = divsteps N (s.d, s.f, s.g) := by
  have hdfg := msteps_dfg N (MSt.init s.d s.f s.g)
  simp only [MSt.init] at hdfg
  rw [← hdfg]
  have hm := msteps_mat (d := s.d) (g := s.g) hf N
  obtain ⟨h1, h2⟩ := hm
  simp only [batch, MSt.init] at h1 h2 ⊢
  have hpos : (0 : Int) < 2 ^ N := by exact Int.pow_pos (by decide)
  rw [← h1, ← h2, Int.mul_ediv_cancel_left _ hpos.ne', Int.mul_ediv_cancel_left _ hpos.ne']

/-- `B` batches are `N B` divsteps. -/
theorem invRun_dfg {N : Nat} {p m x : Int} (hp : p % 2 = 1) :
    ∀ B, ((invRun N p m x B).d, (invRun N p m x B).f, (invRun N p m x B).g) = divsteps (N * B) (1, p, x) ∧
      (invRun N p m x B).f % 2 = 1
  | 0 => ⟨rfl, hp⟩
  | B + 1 => by
    obtain ⟨ih, hodd⟩ := invRun_dfg (N := N) (m := m) (x := x) hp B
    have e := batch_dfg (N := N) (p := p) (m := m) hodd
    simp only [invRun]
    rw [e, ih, show N * (B + 1) = N * B + N by grind, divsteps_add]
    refine ⟨rfl, ?_⟩
    have h := (divsteps_odd (d := 1) (f := p) (g := x) (by decide) hp (N * B + N)).2
    rw [divsteps_add, ← ih, ← e] at h
    exact h

/-- `mredRaw` is exact: `2^64 · mredRaw t = t + k p`, with `k = t m mod 2^64`. -/
theorem mredRaw_spec {p m t : Int} (hm : (p * m + 1) % 2 ^ 64 = 0) :
    2 ^ 64 * mredRaw p m t = t + (t * m) % 2 ^ 64 * p := by
  unfold mredRaw
  apply Int.mul_ediv_cancel'
  -- `t + (t m mod 2^64) p ≡ t + t m p = t (1 + p m) ≡ 0`.
  have h1 : (2 : Int) ^ 64 ∣ p * m + 1 := Int.dvd_of_emod_eq_zero hm
  have h2 : (2 : Int) ^ 64 ∣ t * m - (t * m) % 2 ^ 64 := by
    have := Int.emod_add_ediv_mul (t * m) (2 ^ 64)
    exact ⟨(t * m) / 2 ^ 64, by omega⟩
  have : t + (t * m) % 2 ^ 64 * p = t * (p * m + 1) - (t * m - (t * m) % 2 ^ 64) * p := by grind
  rw [this]
  exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h1) (Int.dvd_mul_of_dvd_left h2)

/-- `2^64 mred t ≡ t` modulo `p`. -/
theorem mred_cong {p m t : Int} (hm : (p * m + 1) % 2 ^ 64 = 0) :
    2 ^ 64 * mred p m t ≡ t [ZMOD p] := by
  have hraw : 2 ^ 64 * mredRaw p m t ≡ t [ZMOD p] := by
    rw [mredRaw_spec hm]; exact Int.add_mul_emod_self_right _ _ _
  have hp0 : 2 ^ 64 * p ≡ 0 [ZMOD p] := Int.modEq_zero_iff_dvd.mpr (dvd_mul_left p _)
  unfold mred norm
  split
  · rw [mul_add]; simpa using hraw.add hp0
  · split
    · rw [mul_sub]; simpa using hraw.sub hp0
    · exact hraw

/-- `mred t` is in `[0, p)` for `|t| < 2^63 p` (with `0 ≤ k < 2^64`). -/
theorem mred_range {p m t : Int} (hp : 0 < p) (hm : (p * m + 1) % 2 ^ 64 = 0) (ht : |t| ≤ 2 ^ 63 * p) :
    0 ≤ mred p m t ∧ mred p m t < p := by
  have hraw := mredRaw_spec (t := t) hm
  have hk0 : 0 ≤ (t * m) % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have hk1 : (t * m) % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
  rw [abs_le'] at ht
  have kl := Int.mul_nonneg hk0 hp.le
  have ku := Int.mul_le_mul_of_nonneg_right (by omega : (t * m) % 2 ^ 64 ≤ 2 ^ 64 - 1) hp.le
  rw [Int.sub_mul] at ku
  -- `-p < mredRaw t < 2p`.
  have lo : -p < mredRaw p m t := by omega
  have hi : mredRaw p m t < 2 * p := by omega
  unfold mred norm
  split
  · constructor <;> omega
  · split <;> constructor <;> omega

/-- The invariant: `f ≡ x a 2^(c i)`, `g ≡ x b 2^(c i)` modulo `p`, `c = 64 - N`, and
`a`, `b` in `[0, p)`. -/
def IState.inv (s : IState) (p x : Int) (K : Int) : Prop :=
  s.f ≡ x * s.a * K [ZMOD p] ∧ s.g ≡ x * s.b * K [ZMOD p] ∧ 0 ≤ s.a ∧ s.a < p ∧ 0 ≤ s.b ∧ s.b < p

/-- `2` is invertible modulo an odd `p`: cancel powers of 2. -/
theorem cancel_pow2 {p a b : Int} {N : Nat} (hp : p % 2 = 1) (hp0 : 0 < p) (h : 2 ^ N * a ≡ 2 ^ N * b [ZMOD p]) :
    a ≡ b [ZMOD p] := by
  have hc : Int.gcd p (2 ^ N) = 1 := Int.gcd_pow_right_of_gcd_eq_one (gcd_two hp)
  have := Int.ModEq.cancel_left_div_gcd (by omega) h
  rwa [hc, Int.ofNat_one, Int.ediv_one] at this

theorem batch_inv {N : Nat} (hN : N ≤ 62) {p m x K : Int} (hp : p % 2 = 1) (hp0 : 0 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0) {s : IState} (hf : s.f % 2 = 1) (h : s.inv p x K) :
    (batch N p m s).inv p x (K * 2 ^ (64 - N)) := by
  obtain ⟨hF, hG, a0, a1, b0, b1⟩ := h
  have hmat := msteps_mat (d := s.d) (g := s.g) hf N
  have hb := msteps_bnd s.d s.f s.g N
  obtain ⟨h1, h2⟩ := hmat
  obtain ⟨bu, bq⟩ := hb
  set t := msteps N (MSt.init s.d s.f s.g) with ht
  have hpos : (0 : Int) < 2 ^ N := by exact Int.pow_pos (by decide)
  have ef : 2 ^ N * ((t.u * s.f + t.v * s.g) / 2 ^ N) = t.u * s.f + t.v * s.g := by
    rw [← h1, Int.mul_ediv_cancel_left _ hpos.ne']
  have eg : 2 ^ N * ((t.q * s.f + t.r * s.g) / 2 ^ N) = t.q * s.f + t.r * s.g := by
    rw [← h2, Int.mul_ediv_cancel_left _ hpos.ne']
  -- The coefficients' products are small.
  have scale : ∀ y a : Int, 0 ≤ a → |y * a| = |y| * a := by
    intro y a ha
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy, abs_of_nonneg (Int.mul_nonneg hy ha)]
    · rw [abs_of_nonpos (by omega : y ≤ 0),
        abs_of_nonpos (Int.mul_nonpos_of_nonpos_of_nonneg (by omega) ha)]
      grind
  have small : ∀ y z : Int, |y| + |z| ≤ 2 ^ N → |y * s.a + z * s.b| ≤ 2 ^ 63 * p := by
    intro y z hyz
    have : |y * s.a + z * s.b| ≤ |y| * p + |z| * p := by
      calc |y * s.a + z * s.b| ≤ |y * s.a| + |z * s.b| := abs_add_le _ _
        _ = |y| * s.a + |z| * s.b := by rw [scale y s.a a0, scale z s.b b0]
        _ ≤ |y| * p + |z| * p := by
          exact add_le_add (Int.mul_le_mul_of_nonneg_left a1.le (abs_nonneg _))
            (Int.mul_le_mul_of_nonneg_left b1.le (abs_nonneg _))
    have h62 : (2 : Int) ^ N ≤ 2 ^ 63 := (Int.pow_lt_pow_of_lt (by decide) (by omega)).le
    have := Int.mul_le_mul_of_nonneg_right (Int.le_trans hyz h62) hp0.le
    rw [Int.add_mul] at this
    omega
  have rA := mred_range hp0 hm (small t.u t.v bu)
  have rB := mred_range hp0 hm (small t.q t.r bq)
  have cA := mred_cong (p := p) (t := t.u * s.a + t.v * s.b) hm
  have cB := mred_cong (p := p) (t := t.q * s.a + t.r * s.b) hm
  have e64 : (2 : Int) ^ 64 = 2 ^ N * 2 ^ (64 - N) := by rw [← pow_add]; congr 1; omega
  refine ⟨?_, ?_, rA.1, rA.2, rB.1, rB.2⟩
  · apply cancel_pow2 (N := N) hp hp0
    show 2 ^ N * ((t.u * s.f + t.v * s.g) / 2 ^ N) ≡ _ [ZMOD p]
    rw [ef]
    calc t.u * s.f + t.v * s.g ≡ t.u * (x * s.a * K) + t.v * (x * s.b * K) [ZMOD p] :=
          (hF.mul_left _).add (hG.mul_left _)
      _ = x * K * (t.u * s.a + t.v * s.b) := by grind
      _ ≡ x * K * (2 ^ 64 * mred p m (t.u * s.a + t.v * s.b)) [ZMOD p] := (cA.symm.mul_left _)
      _ = 2 ^ N * (x * mred p m (t.u * s.a + t.v * s.b) * (K * 2 ^ (64 - N))) := by rw [e64]; grind
  · apply cancel_pow2 (N := N) hp hp0
    show 2 ^ N * ((t.q * s.f + t.r * s.g) / 2 ^ N) ≡ _ [ZMOD p]
    rw [eg]
    calc t.q * s.f + t.r * s.g ≡ t.q * (x * s.a * K) + t.r * (x * s.b * K) [ZMOD p] :=
          (hF.mul_left _).add (hG.mul_left _)
      _ = x * K * (t.q * s.a + t.r * s.b) := by grind
      _ ≡ x * K * (2 ^ 64 * mred p m (t.q * s.a + t.r * s.b)) [ZMOD p] := (cB.symm.mul_left _)
      _ = 2 ^ N * (x * mred p m (t.q * s.a + t.r * s.b) * (K * 2 ^ (64 - N))) := by rw [e64]; grind

/-- The invariant through `B` batches. -/
theorem invRun_inv {N : Nat} (hN : N ≤ 62) {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0) : ∀ B, (invRun N p m x B).inv p x (2 ^ ((64 - N) * B))
  | 0 => by
    refine ⟨?_, ?_, le_refl _, by simp only [invRun]; omega, by simp [invRun], by simp only [invRun]; omega⟩
    · simp only [invRun, mul_zero, pow_zero, mul_one]
      exact Int.emod_self.trans (by simp)
    · simp [invRun, Int.ModEq]
  | B + 1 => by
    have := batch_inv hN hp (by omega) hm ((invRun_dfg (N := N) (m := m) (x := x) hp B).2) (invRun_inv hN hp hp1 hm B)
    simp only [invRun]
    rw [show (64 - N) * (B + 1) = (64 - N) * B + (64 - N) by grind, pow_add]
    exact this

/-- After enough batches, `f = ±1` and `x (± a) 2^(c B) ≡ 1` modulo `p`, if
`gcd(p, x) = 1`. -/
theorem invRun_spec {N B : Nat} (hN : N ≤ 62) {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0)
    (hdone : (divsteps (N * B) (1, p, x)).2.2 = 0 ∧ (divsteps (N * B) (1, p, x)).2.1.natAbs = Int.gcd p x)
    (hg : Int.gcd p x = 1) :
    ((invRun N p m x B).f = 1 ∨ (invRun N p m x B).f = -1) ∧
      x * ((invRun N p m x B).f * (invRun N p m x B).a) * 2 ^ ((64 - N) * B) ≡ 1 [ZMOD p] := by
  have hd := (invRun_dfg (N := N) (m := m) (x := x) hp B).1
  have hI := invRun_inv (x := x) hN hp hp1 hm B
  set s := invRun N p m x B
  have hfa : s.f.natAbs = 1 := by
    have : s.f = (divsteps (N * B) (1, p, x)).2.1 := by rw [← hd]
    rw [this, hdone.2, hg]
  have hf1 : s.f = 1 ∨ s.f = -1 := by omega
  refine ⟨hf1, ?_⟩
  -- `f ≡ x a 2^(c B)` and `f² = 1`.
  have := hI.1.mul_left s.f
  have hf2 : s.f * s.f = 1 := by rcases hf1 with h | h <;> rw [h] <;> decide
  rw [hf2] at this
  have e : s.f * (x * s.a * 2 ^ ((64 - N) * B)) = x * (s.f * s.a) * 2 ^ ((64 - N) * B) := by grind
  rw [← e]; exact this.symm

end VG.Proof.Divstep
