module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleTest

/-! # The sampler changes only its input slots, comparison temporary and flag -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Mont
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def sampleArithmeticWrites (n : Nat) : List (Nat × Nat) := (slot n 5, 8 * n) :: sampleTestWrites n

def sampleWrites (base : Addr) (n : Nat) (p : Addr) (len : Nat) : List Region :=
  (sampleArithmeticWrites n).map (fun r => ⟨off base r.1, r.2⟩) ++ [⟨p, len⟩]

theorem sampleArithmetic_bound {n size : Nat} (width : n ≤ 48) (room : primeIsUniform + 4 ≤ size) :
    ∀ r ∈ sampleArithmeticWrites n, r.1 + r.2 ≤ size := by
  intro r hr
  simp only [sampleArithmeticWrites, sampleTestWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride, primeIsUniform] at * <;> omega
end VG.Proof.Dsa.X86.Generation
