module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.VerifyVerified
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
# Ed448 verification on PPC64LE

The signature and documentation come from the reviewed Ed448 API. The
reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`) is passed to the proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448Verify.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed448.verifyApi.artifact PPC64LE.target {
    code := Impl.Ed448.PPC64LE.Whole.verifyCode
    stack := 352
    verified := Proof.Ed448.PPC64LE.Whole.verify_framed Proof.Ed448.recover_ok Proof.Ed448.verifyEq4_ok }]

end VG.Artifacts.Ed448Verify.PPC64LE
