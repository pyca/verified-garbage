import VerifiedGarbage.Proof.Divstep.Alg

namespace VG.Proof.Divstep

/-- An observed zero remainder suffices for convergence; no worst-case step bound is needed. -/
theorem invRun_done_of_g_zero {N B : Nat} {p m x : Int} (hp : p % 2 = 1)
    (hz : (invRun N p m x B).g = 0) :
    (divsteps (N * B) (1, p, x)).2.2 = 0 ∧
      (divsteps (N * B) (1, p, x)).2.1.natAbs = Int.gcd p x := by
  have hd := (invRun_dfg (N := N) (m := m) (x := x) hp B).1
  have hg : (divsteps (N * B) (1, p, x)).2.2 = 0 := by rw [← hd]; exact hz
  refine ⟨hg, ?_⟩
  have h := divsteps_gcd (d := 1) (g := x) (by decide) hp (N * B)
  rw [hg, Int.gcd_zero_right] at h
  exact h

/-- Early convergence has the same inverse relation and scale as any completed batch count. -/
theorem invRun_spec_of_g_zero {N B : Nat} (hN : N ≤ 62) {p m x : Int}
    (hp : p % 2 = 1) (hp1 : 1 < p) (hm : (p * m + 1) % 2 ^ 64 = 0)
    (hz : (invRun N p m x B).g = 0) (hg : Int.gcd p x = 1) :
    ((invRun N p m x B).f = 1 ∨ (invRun N p m x B).f = -1) ∧
      x * ((invRun N p m x B).f * (invRun N p m x B).a) * 2 ^ ((64 - N) * B) ≡ 1 [ZMOD p] :=
  invRun_spec hN hp hp1 hm (invRun_done_of_g_zero hp hz) hg

end VG.Proof.Divstep
