module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombMixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombOut
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward.CombArithmetic

theorem cases : Cases
  | .mixed => CombMixed.caseProof
  | .out => CombOut.caseProof

theorem compiler_correct {size : Nat} (hsize : 8192≤size) :
    FieldCompilerCorrect VG.Impl.P256.CombArithmetic.program size := by
  intro M base m _ Sl hL hAl hm ops V E s hi hS hLo hV
  exact field_ok cases hL hAl hm hsize ops hi hS hLo hV

end VG.Proof.Weierstrass.AArch64.Forward.CombArithmetic
