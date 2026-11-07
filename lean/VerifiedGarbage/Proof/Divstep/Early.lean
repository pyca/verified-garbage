module

public import VerifiedGarbage.Proof.Divstep.Alg

@[expose] public section

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

end VG.Proof.Divstep
