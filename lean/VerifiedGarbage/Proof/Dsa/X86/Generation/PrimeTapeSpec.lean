module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRun
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeWitnessSpec

/-! # Candidate preparation may change scratch without changing the witness-loop result -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG

theorem primeStepResult_tape {G : PrimeConfig} {s t : Mem} (used uniform : Nat)
    (tape : Spec.Rsa.bytesAt t (G.tape.setWidth 64) G.tapeLen =
      Spec.Rsa.bytesAt s (G.tape.setWidth 64) G.tapeLen) :
    primeStepResult G t used uniform = primeStepResult G s used uniform := by
  unfold primeStepResult
  split
  · rename_i full
    rw [primeDrawValue_spec t full, primeDrawValue_spec s full, tape]
  · rfl

theorem primeRun_tape {G : PrimeConfig} {s t : Mem} (used uniform : Nat)
    (tape : Spec.Rsa.bytesAt t (G.tape.setWidth 64) G.tapeLen =
      Spec.Rsa.bytesAt s (G.tape.setWidth 64) G.tapeLen) :
    primeRun G t used uniform = primeRun G s used uniform := by
  conv => lhs; rw [primeRun]
  conv => rhs; rw [primeRun]
  rw [primeStepResult_tape used uniform tape]
  split
  · exact primeRun_tape _ _ tape
  · rfl
termination_by G.tapeLen - used
decreasing_by
  have h := primeStepResult_continue ‹(primeStepResult G s used uniform).status = 4›
  omega
end VG.Proof.Dsa.X86.Generation
