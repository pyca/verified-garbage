module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Policy
import VerifiedGarbage.Proof.Framework.Omega

/-! The attempt budget needs u64, while all native pointers, lengths and refill requests fit u32. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem SearchParams.policy (p : SearchParams) : Policy p.c.bits := ⟨p.c.minBits, p.c.maxBits⟩

theorem SearchParams.attempts_bound (p : SearchParams) : p.attempts ≤ 2 ^ 32 :=
  Nat.le_trans p.attemptsBound p.policy.attempts_bound

theorem SearchParams.entropy_bound (p : SearchParams) : Spec.Ffdh.parameterEntropy p.c.bits ≤ 33555456 :=
  p.policy.entropy_bound

theorem SearchParams.entropy_fits (p : SearchParams) : Spec.Ffdh.parameterEntropy p.c.bits < 2 ^ 32 := by
  have := p.entropy_bound
  omega

theorem SearchParams.width_bounds (p : SearchParams) : 64 ≤ p.c.length ∧ p.c.length ≤ 1024 :=
  p.policy.width_bounds

theorem SearchParams.capacity_fits (p : SearchParams) : p.c.capacity < 2 ^ 32 := by
  have := p.c.scratchFits
  omega

theorem SearchLive.used_fits {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) : used < 2 ^ 32 := Nat.lt_of_le_of_lt h.usedBound p.c.tapeCount

theorem SearchLive.remaining_bound {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) : remaining ≤ 2 ^ 32 := Nat.le_trans h.remainingBound p.attempts_bound

end VG.Proof.Ffdh.Arm.ParameterSearch
