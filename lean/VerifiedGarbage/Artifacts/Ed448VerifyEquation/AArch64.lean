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
    notes := ["Uses baseline integer instructions and NEON field arithmetic. Accumulates \
      encoding, canonical scalar and equation checks in x20. Decodes A and R with the \
      existing square-root chain, and computes [S]B + [k](-A) with a shared doubling loop: \
      width-eight signed digits select 64 odd affine base multiples from an 8 KiB static, \
      and width-five signed digits select eight odd projective key multiples built in \
      scratch. Zero digits skip additions; leading zero pairs skip doublings. These \
      branches and direct table addresses depend only on the public verification scalars. \
      Both full 456-bit inputs are retained. Compares the four cofactored projective cross \
      products with [4]R, preserving the existing invalid-input behavior and 8192-byte \
      scratch contract. Saves and restores callee-saved registers in scratch."]
    consts := Impl.Ed448.AArch64.Sparse.baseConsts
    code := Impl.Ed448.AArch64.Sparse.verifyEquation
    verified := Proof.Ed448.AArch64.Sparse.verifyEquation_verified Proof.Ed448.recover_ok }]

end VG.Artifacts.Ed448VerifyEquation.AArch64
