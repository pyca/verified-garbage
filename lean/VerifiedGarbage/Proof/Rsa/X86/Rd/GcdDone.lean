module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.GcdW
import VerifiedGarbage.Proof.Rsa.Divstep.Bound
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import VerifiedGarbage.Proof.Divstep.Alg32
import VerifiedGarbage.Proof.Framework.Omega

/-! # The fused GCD's convergence on i686 (`GcdDone`)

After any `steps ≥ 80 (n + 1) + 1` divsteps the run from `(1, p, oddInput p x)` has `g = 0` and
`|f| = gcd(p, x)` (`done_words`), so after `3 (n + 1)` batches of thirty. A separate module, imported by the
registration alone, so that the bound's algebra stays out of the proofs that use it.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover.G

open VG.Proof.Rsa.Divstep (oddInput)
open VG.Proof.Rsa.X86.InvBatchRt.F (rs)

/-- The run has converged after any `steps ≥ 80 (n + 1) + 1` divsteps, for `p, x < 2^(32 n)`. -/
theorem oddInput_done_ge {m x n steps : Nat} (hm : m % 2 = 1)
    (hmR : m < 2 ^ (32 * n)) (hxR : x < 2 ^ (32 * n)) (hs : 80 * (n + 1) + 1 ≤ steps) :
    (Divstep.divsteps steps (1, m, oddInput m x)).2.2 = 0 ∧
      (Divstep.divsteps steps (1, m, oddInput m x)).2.1.natAbs = Nat.gcd m x := by
  have grow : 2 * 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 1)) := by
    rw [show 32 * (n + 1) = 32 * n + 32 by omega_using [], pow_add]; omega_using []
  have h := VG.Proof.Rsa.Divstep.done_words (w := n + 1) (steps := steps) (by omega_using [])
    (by exact_mod_cast hm) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    (Or.inr (by exact_mod_cast VG.Proof.Rsa.Divstep.oddInput_odd (x := x) hm))
    (by exact_mod_cast (hmR.le.trans (by omega_using [grow] : 2 ^ (32 * n) ≤ 2 ^ (32 * (n + 1)))))
    (by exact_mod_cast ((VG.Proof.Rsa.Divstep.oddInput_lt hmR hxR).le.trans grow)) hs
  rw [Int.gcd_natCast_natCast, VG.Proof.Rsa.Divstep.oddInput_gcd] at h
  exact h

/-- After `j ≥ 3 (n + 1)` batches, `g = 0` and `|f| = gcd(p, x)`. -/
theorem rs_done' {p iv x n j : Nat} (odd : p % 2 = 1) (pc : p < 2 ^ (32 * n)) (xc : x < 2 ^ (32 * n))
    (hj : 3 * (n + 1) ≤ j) : (rs p iv x j).g = 0 ∧ (rs p iv x j).f.natAbs = Nat.gcd p x := by
  have oddI : (p : Int) % 2 = 1 := by exact_mod_cast odd
  have e := (Divstep.W32.invRun_dfg (N := 30) (m := (iv : Int)) (x := (oddInput p x : Int)) oddI j).1
  have d := oddInput_done_ge (steps := 30 * j) odd pc xc (by omega_using [hj])
  rw [← e] at d
  exact d

instance gcdDone : GcdDone := ⟨fun odd pc xc hj => rs_done' odd pc xc hj⟩

end VG.Proof.Rsa.X86.Recover.G
