module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Timing
import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Sat

/-! Exact certified imports share the original validation, timing, and ABI contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE

theorem verified : Verified target VG.Impl.Ffdh.PPC64LE.VettedValidation.code contract :=
  ⟨correct, constantTime, sat⟩

end VG.Proof.Ffdh.PPC64LE.VettedValidation
