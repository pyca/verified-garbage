module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Timing
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Sat

/-! Every selected Montgomery backend inherits the same certified standard-domain fast path. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem verified (v : RoundImpl) : Verified target (emittedCode v) contract :=
  ⟨correct v, constantTime v, sat⟩

end VG.Proof.Ffdh.X86_64.VettedValidation
