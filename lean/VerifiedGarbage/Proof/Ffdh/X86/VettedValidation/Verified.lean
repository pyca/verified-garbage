module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Correct
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Timing
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Sat

/-! Exact certified imports share the original validation, timing, and ABI contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86

theorem verified : Verified target VG.Impl.Ffdh.X86.VettedValidation.code contract :=
  ⟨correct, constantTime, sat⟩

end VG.Proof.Ffdh.X86.VettedValidation
