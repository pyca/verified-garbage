module

public import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 verification's equation on ARMv7

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only
registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448VerifyEquation.Arm

def artifacts : List Artifact := [
  Spec.Ed448.verifyEquationApi.artifact Arm.target {
    code := Impl.Ed448.Arm.verifyEquation
    verified := Proof.Ed448.Arm.verifyEquation_verified Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok
    stack := 0 }]

end VG.Artifacts.Ed448VerifyEquation.Arm
