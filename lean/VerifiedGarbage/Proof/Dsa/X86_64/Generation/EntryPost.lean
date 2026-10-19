module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryRun

/-! # The entry result meets the shared parameter-generation postcondition -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem entry_shared_post {s t : State} (h : EntryResult s t) :
    (Spec.Dsa.generateParametersContract abi 472).post s t := by
  sig_post [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_post [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  refine ⟨?_, h.bytes⟩
  rw [h.status]
  change (BitVec.setWidth 32 (BitVec.ofNat 64 (Spec.Dsa.signStatus (abiResult s)))).toNat = Spec.Dsa.signStatus (abiResult s)
  cases abiResult s <;> rfl

end VG.Proof.Dsa.X86_64.Generation
