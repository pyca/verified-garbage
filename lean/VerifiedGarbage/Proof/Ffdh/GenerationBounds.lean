module
public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.Proof.EntropyRequest

import VerifiedGarbage.Proof.Ffdh.GenerationTape
import VerifiedGarbage.Proof.Framework.Omega

/-! # Native generation control: byte accounting and bounded persistent state -/

@[expose] public section

namespace VG.Proof.Ffdh.Generation

open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen

theorem consume_assoc (result : ParameterSearchResult) (a b : Nat) :
    (result.consume b).consume a = result.consume (a + b) := by
  cases result <;> simp only [ParameterSearchResult.consume, Nat.add_assoc]

theorem consume_zero (result : ParameterSearchResult) : result.consume 0 = result := by
  cases result <;> simp only [ParameterSearchResult.consume, Nat.zero_add]

end VG.Proof.Ffdh.Generation
