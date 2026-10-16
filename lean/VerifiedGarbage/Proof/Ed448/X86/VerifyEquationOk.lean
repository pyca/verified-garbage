module

public import VerifiedGarbage.Proof.Ed448.X86.Callee
public import VerifiedGarbage.Proof.Ed448.X86.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Ed448.X86.VerifyCT
public import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
public import VerifiedGarbage.Proof.Sha3.X86.Lit

/-!
# Ed448 on x86: `vg_ed448_verify_equation` for its caller

What `vg_ed448_verify`'s proof takes of `vg_ed448_verify_equation`: its
correctness, from the reference computations' agreement with the specification
(`Proof/Ed448/Facts.lean`), its constant time, and that it keeps the stack
pointer and uses no stack, for `Artifacts/Ed448Verify/X86.lean`. Like
`Facts.lean`, only registration files import this module.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG.X86

/-- `vg_ed448_verify_equation` meets what its caller takes of it. -/
theorem verifyEquation_calleeOk :
    CalleeOk verifyEquationLocal Impl.Ed448.X86.verifyEquation :=
  ⟨verifyEquation_ok Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok,
    verifyEquation_ct Proof.Ed448.recover_ok, NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ed448.X86
