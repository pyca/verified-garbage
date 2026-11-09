module

public import VerifiedGarbage.Proof.RsaKeyGen.MrIter

/-! # Exact blinded and uniform witness counters -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG VG.Spec.RsaKeyGen

instance goSDecidable (checks : Nat) (s : Nat × Nat) : Decidable (goS checks s) :=
  inferInstanceAs (Decidable (s.1 ≤ blindedChecks ∨ s.2 < checks))

end VG.Proof.RsaKeyGen
