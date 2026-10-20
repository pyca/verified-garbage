module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeStep
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTape

/-! # A terminating model of the native public-input witness loop -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG

theorem primeStepResult_continue {G : PrimeConfig} {mem : Mem} {used uniform : Nat}
    (more : (primeStepResult G mem used uniform).status = 4) :
    used < (primeStepResult G mem used uniform).used ∧
    (primeStepResult G mem used uniform).used ≤ G.tapeLen ∧
    (primeStepResult G mem used uniform).uniform < G.checks := by
  have positive : 0 < G.draw := by have := G.lenMin; unfold PrimeConfig.draw PrimeConfig.n; omega
  unfold primeStepResult at *
  split at more
  · rename_i full
    simp only [full, ite_true]
    dsimp only at more ⊢
    unfold primeResultStatus at more
    split at more
    · rename_i passed
      split at more
      · rename_i enough
        simp only [passed, ite_true]
        exact ⟨by omega, trivial, enough⟩
      · contradiction
    · contradiction
  · contradiction

def primeRun (G : PrimeConfig) (mem : Mem) (used uniform : Nat) : PrimeStepResult :=
  let next := primeStepResult G mem used uniform
  if _more : next.status = 4 then primeRun G mem next.used next.uniform else next
termination_by G.tapeLen - used
decreasing_by
  have h := primeStepResult_continue _more
  omega

theorem primeStepResult_frame {G : PrimeConfig} {s t : Mem} {used uniform : Nat}
    (O : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s t) :
    primeStepResult G t used uniform = primeStepResult G s used uniform := by
  unfold primeStepResult
  split
  · rename_i full
    have enough : G.len ≤ G.draw := by unfold PrimeConfig.draw PrimeConfig.n; omega
    have bytes := O.tapeBytes (start := used + (G.draw - G.len)) (len := G.len) (by omega)
    simp only [primeDrawValue, bytes]
    rfl
  · rfl

theorem primeRun_frame {G : PrimeConfig} {s t : Mem} {used uniform : Nat}
    (O : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s t) :
    primeRun G t used uniform = primeRun G s used uniform := by
  conv => lhs; rw [primeRun]
  conv => rhs; rw [primeRun]
  rw [primeStepResult_frame O]
  split
  · exact primeRun_frame O
  · rfl
termination_by G.tapeLen - used
decreasing_by
  have h := primeStepResult_continue ‹(primeStepResult G s used uniform).status = 4›
  omega

end VG.Proof.Dsa.X86.Generation
