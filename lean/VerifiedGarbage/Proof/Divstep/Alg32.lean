import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Word32
import VerifiedGarbage.Proof.Divstep.Mred32

/-!
# Inversion by batches of divsteps

The inverse of `x` modulo an odd `p` (`0 ≤ x < p`), as the code computes it
(`invRun`): from `(d, f, g) = (1, p, x)` and coefficients `(a, b) = (0, 1)`,
each batch takes the matrix `(u, v, q, r)` of `N` divsteps, replaces
`(f, g)` by `(u f + v g, q f + r g) / 2^N` (exactly: `batch_dfg`), and
`(a, b)` by `(u a + v b, q a + r b) / 2^32 mod p` (`mred`, adding the multiple
of `p` that clears the low word, then at most one `p` back into `[0, p)`).
With `f ≡ x a 2^(c i)` and `g ≡ x b 2^(c i)` modulo `p`, `c = 32 - N`
(`invRun_inv`), once `g = 0`, `f = ±gcd(p, x) = ±1`, and
`x (± a) 2^(c i) ≡ 1` (`invRun_spec`).
-/

namespace VG.Proof.Divstep.W32

/-- A batch's `(d, f, g)` are `N` divsteps'. -/
theorem batch_dfg {N : Nat} {p m : Int} {s : IState} (hf : s.f % 2 = 1) :
    ((batch N p m s).d, (batch N p m s).f, (batch N p m s).g) = divsteps N (s.d, s.f, s.g) := by
  have hdfg := msteps_dfg N (MSt.init s.d s.f s.g)
  simp only [MSt.init] at hdfg
  rw [← hdfg]
  have hm := msteps_mat (d := s.d) (g := s.g) hf N
  obtain ⟨h1, h2⟩ := hm
  simp only [batch, MSt.init] at h1 h2 ⊢
  have hpos : (0 : Int) < 2 ^ N := by positivity
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
    rw [e, ih, show N * (B + 1) = N * B + N by ring, divsteps_add]
    refine ⟨rfl, ?_⟩
    have h := (divsteps_odd (d := 1) (f := p) (g := x) (by decide) hp (N * B + N)).2
    rw [divsteps_add, ← ih, ← e] at h
    exact h

/-- The invariant: `f ≡ x a 2^(c i)`, `g ≡ x b 2^(c i)` modulo `p`, `c = 32 - N`, and
`a`, `b` in `[0, p)`. -/
def IState.inv (s : IState) (p x : Int) (K : Int) : Prop :=
  s.f ≡ x * s.a * K [ZMOD p] ∧ s.g ≡ x * s.b * K [ZMOD p] ∧ 0 ≤ s.a ∧ s.a < p ∧ 0 ≤ s.b ∧ s.b < p

/-- `2` is invertible modulo an odd `p`: cancel powers of 2. -/
theorem cancel_pow2 {p a b : Int} {N : Nat} (hp : p % 2 = 1) (hp0 : 0 < p) (h : 2 ^ N * a ≡ 2 ^ N * b [ZMOD p]) :
    a ≡ b [ZMOD p] := by
  have hc : Int.gcd p (2 ^ N) = 1 := Int.gcd_pow_right_of_gcd_eq_one (gcd_two hp)
  have := Int.ModEq.cancel_left_div_gcd (by omega) h
  rwa [hc, Int.ofNat_one, Int.ediv_one] at this

theorem batch_inv {N : Nat} (hN : N ≤ 30) {p m x K : Int} (hp : p % 2 = 1) (hp0 : 0 < p)
    (hm : (p * m + 1) % 2 ^ 32 = 0) {s : IState} (hf : s.f % 2 = 1) (h : s.inv p x K) :
    (batch N p m s).inv p x (K * 2 ^ (32 - N)) := by
  obtain ⟨hF, hG, a0, a1, b0, b1⟩ := h
  have hmat := msteps_mat (d := s.d) (g := s.g) hf N
  have hb := msteps_bnd s.d s.f s.g N
  obtain ⟨h1, h2⟩ := hmat
  obtain ⟨bu, bq⟩ := hb
  set t := msteps N (MSt.init s.d s.f s.g) with ht
  have hpos : (0 : Int) < 2 ^ N := by positivity
  have ef : 2 ^ N * ((t.u * s.f + t.v * s.g) / 2 ^ N) = t.u * s.f + t.v * s.g := by
    rw [← h1, Int.mul_ediv_cancel_left _ hpos.ne']
  have eg : 2 ^ N * ((t.q * s.f + t.r * s.g) / 2 ^ N) = t.q * s.f + t.r * s.g := by
    rw [← h2, Int.mul_ediv_cancel_left _ hpos.ne']
  -- The coefficients' products are small.
  have small : ∀ y z : Int, |y| + |z| ≤ 2 ^ N → |y * s.a + z * s.b| ≤ 2 ^ 31 * p := by
    intro y z hyz
    have : |y * s.a + z * s.b| ≤ |y| * p + |z| * p := by
      calc |y * s.a + z * s.b| ≤ |y * s.a| + |z * s.b| := abs_add_le _ _
        _ = |y| * |s.a| + |z| * |s.b| := by rw [abs_mul, abs_mul]
        _ ≤ |y| * p + |z| * p := by
          rw [abs_of_nonneg a0, abs_of_nonneg b0]
          exact add_le_add (mul_le_mul_of_nonneg_left a1.le (abs_nonneg _))
            (mul_le_mul_of_nonneg_left b1.le (abs_nonneg _))
    have h30 : (2 : Int) ^ N ≤ 2 ^ 31 := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have rA := mred_range hp0 hm (small t.u t.v bu)
  have rB := mred_range hp0 hm (small t.q t.r bq)
  have cA := mred_cong (p := p) (t := t.u * s.a + t.v * s.b) hm
  have cB := mred_cong (p := p) (t := t.q * s.a + t.r * s.b) hm
  have e32 : (2 : Int) ^ 32 = 2 ^ N * 2 ^ (32 - N) := by rw [← pow_add]; congr 1; omega
  refine ⟨?_, ?_, rA.1, rA.2, rB.1, rB.2⟩
  · apply cancel_pow2 (N := N) hp hp0
    show 2 ^ N * ((t.u * s.f + t.v * s.g) / 2 ^ N) ≡ _ [ZMOD p]
    rw [ef]
    calc t.u * s.f + t.v * s.g ≡ t.u * (x * s.a * K) + t.v * (x * s.b * K) [ZMOD p] :=
          (hF.mul_left _).add (hG.mul_left _)
      _ = x * K * (t.u * s.a + t.v * s.b) := by ring
      _ ≡ x * K * (2 ^ 32 * mred p m (t.u * s.a + t.v * s.b)) [ZMOD p] := (cA.symm.mul_left _)
      _ = 2 ^ N * (x * mred p m (t.u * s.a + t.v * s.b) * (K * 2 ^ (32 - N))) := by rw [e32]; ring
  · apply cancel_pow2 (N := N) hp hp0
    show 2 ^ N * ((t.q * s.f + t.r * s.g) / 2 ^ N) ≡ _ [ZMOD p]
    rw [eg]
    calc t.q * s.f + t.r * s.g ≡ t.q * (x * s.a * K) + t.r * (x * s.b * K) [ZMOD p] :=
          (hF.mul_left _).add (hG.mul_left _)
      _ = x * K * (t.q * s.a + t.r * s.b) := by ring
      _ ≡ x * K * (2 ^ 32 * mred p m (t.q * s.a + t.r * s.b)) [ZMOD p] := (cB.symm.mul_left _)
      _ = 2 ^ N * (x * mred p m (t.q * s.a + t.r * s.b) * (K * 2 ^ (32 - N))) := by rw [e32]; ring

/-- The invariant through `B` batches. -/
theorem invRun_inv {N : Nat} (hN : N ≤ 30) {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p)
    (hm : (p * m + 1) % 2 ^ 32 = 0) : ∀ B, (invRun N p m x B).inv p x (2 ^ ((32 - N) * B))
  | 0 => by
    refine ⟨?_, ?_, le_refl _, by simp only [invRun]; omega, by simp [invRun], by simp only [invRun]; omega⟩
    · simp only [invRun, mul_zero, pow_zero, mul_one]
      exact Int.emod_self.trans (by simp)
    · simp [invRun, Int.ModEq]
  | B + 1 => by
    have := batch_inv hN hp (by omega) hm ((invRun_dfg (N := N) (m := m) (x := x) hp B).2) (invRun_inv hN hp hp1 hm B)
    simp only [invRun]
    rw [show (32 - N) * (B + 1) = (32 - N) * B + (32 - N) by ring, pow_add]
    exact this

/-- After enough batches, `f = ±1` and `x (± a) 2^(c B) ≡ 1` modulo `p`, if
`gcd(p, x) = 1`. -/
theorem invRun_spec {N B : Nat} (hN : N ≤ 30) {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p)
    (hm : (p * m + 1) % 2 ^ 32 = 0)
    (hdone : (divsteps (N * B) (1, p, x)).2.2 = 0 ∧ (divsteps (N * B) (1, p, x)).2.1.natAbs = Int.gcd p x)
    (hg : Int.gcd p x = 1) :
    ((invRun N p m x B).f = 1 ∨ (invRun N p m x B).f = -1) ∧
      x * ((invRun N p m x B).f * (invRun N p m x B).a) * 2 ^ ((32 - N) * B) ≡ 1 [ZMOD p] := by
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
  have hf2 : s.f * s.f = 1 := by rcases hf1 with h | h <;> rw [h] <;> norm_num
  rw [hf2] at this
  have e : s.f * (x * s.a * 2 ^ ((32 - N) * B)) = x * (s.f * s.a) * 2 ^ ((32 - N) * B) := by ring
  rw [← e]; exact this.symm

end VG.Proof.Divstep.W32
