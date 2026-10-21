module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSeparation

/-! # The shared precondition establishes the native key environment -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

theorem call_valid {s : State} (h : contract.pre s) : (callEnvironment s).Valid := by
  have Z := call_sizes h
  have A := call_layout h
  have D := call_separation h
  refine ⟨Z.length, Z.exponentLength, ?_, A.workspaceFit, ?_, A.exponentFit, ?_, ?_, D.exponentScratch, ?_⟩
  · change Spec.Rsa.scratchWords (2 * (arg s 5).toNat) ≤ (arg s 17).toNat
    rw [← Z.modulus]
    exact Z.capacity
  · intro i hi
    exact A.outFit Z hi
  · intro i hi
    rw [Z.outputRegion hi]
    exact D.outputScratch i hi
  · intro i hi j hj different
    rw [Z.outputRegion hi, Z.outputRegion hj]
    by_cases order : i < j
    · exact D.outputSeparate i hi j hj order
    · exact (D.outputSeparate j hj i hi (by omega)).symm
  · intro i hi
    rw [Z.outputRegion hi]
    exact D.exponentOutput i hi

end VG.Proof.RsaKeyGen.X86.Key
