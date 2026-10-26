module

public import VerifiedGarbage.Proof.Ed448.X86.Callee
import VerifiedGarbage.Proof.Ed448.X86.BaseVerified
import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed448.X86.BaseCT
public import VerifiedGarbage.Proof.Ed448.X86.BaseLit
public import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
import Mathlib.FieldTheory.Finite.Basic
public import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X448.X86.Step

/-!
# Ed448 on x86: `vg_ed448_scalar_base` for its callers

What a caller's proof takes of `vg_ed448_scalar_base`: its correctness, from the
reference ladder's agreement with the specification (`Proof/Ed448/Facts.lean`),
its constant time, and that it keeps the stack pointer and uses no stack, for
`Artifacts/Ed448PublicKey/X86.lean` and `Artifacts/Ed448SignCached/X86.lean`.
Like `Facts.lean`, only registration files import this module.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG.X86

/-- `vg_ed448_scalar_base` meets what its callers take of it. -/
theorem scalarBase_calleeOk : CalleeOk scalarBaseLocal Impl.Ed448.X86.scalarBase :=
  ⟨scalarBase_ok Proof.Ed448.baseLadder_ok, scalarBase_ct,
    NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ed448.X86
