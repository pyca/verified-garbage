module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Verified
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
# Ed448 verification's equation on AArch64

The signature and documentation come from the reviewed Ed448 API. Decoding's
agreement with the specification (`Proof/Ed448/Facts.lean`) is passed to the
proof here, so that only registration files import it.
-/

@[expose] public section

namespace VG.Artifacts.Ed448VerifyEquation.AArch64

def artifacts : List Artifact := [
  Spec.Ed448.verifyEquationApi.artifact AArch64.target {
    consts := Impl.Ed448.AArch64.Sparse.baseConsts
    code := Impl.Ed448.AArch64.Sparse.verifyEquation
    verified := Proof.Ed448.AArch64.Sparse.verifyEquation_verified Proof.Ed448.recover_ok }]

end VG.Artifacts.Ed448VerifyEquation.AArch64
