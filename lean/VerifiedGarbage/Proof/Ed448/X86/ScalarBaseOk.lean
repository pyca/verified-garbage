module

public import VerifiedGarbage.Proof.Ed448.X86.Callee
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
public import VerifiedGarbage.Proof.Ed448.CombRef
public import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
public import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Ed448.X86.BaseCT
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.CombFacts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Ed448.X86.BaseLit
public import VerifiedGarbage.Proof.Sha3.X86.Lit
import Mathlib.FieldTheory.Finite.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X448.X86.Step

/-! ### `Ed448.X86.BaseVerified`, which only this module used -/

section

/-!
# Ed448 base-point multiplication on x86 (32-bit): `Verified`

Correctness (`BaseMain.lean`), constant time (`BaseCT.lean`),
satisfiability, and the shared contract of `Spec/` with the 20 bytes of stack
below the return address that the calls of the field functions use, given that the comb the
code computes encodes as `[k]B` (`Proof.Ed448.BaseCombOk`, proven with the
group law in `Proof/Ed448/CombFacts.lean`, which only the registration file
imports). The local contract only reads the arguments; the shared one lets
the code write them too (`writeArgs`), which it does not
(`Verified.narrowTo`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (BaseCombOk decodeLE_below)
open VG.Impl.Ed448.X86 (scalarBase)

theorem scalarBase_ok (hl : BaseCombOk) (s : State) (h : scalarBaseLocal.pre s) :
    ∃ tr t, Exec isa scalarBase s tr t ∧ abiPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨tr, t, he, h1, h2⟩ := scalarBase_comb (BasePre.of h)
  refine ⟨tr, t, he, h1, ?_⟩
  change Spec.Ed448.bytesAt t.mem _ 57 =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul _ Spec.Ed448.basePoint)
  rw [h2, hl _ (decodeLE_below (by simp [Spec.Ed448.bytesAt]))]

end VG.Proof.Ed448.X86

end

end


/-!
# Ed448 on x86: `vg_ed448_scalar_base` for its callers

What a caller's proof takes of `vg_ed448_scalar_base`: its correctness, from the
reference comb's agreement with the specification (`Proof/Ed448/CombFacts.lean`),
its constant time, and that it keeps the stack pointer and uses no stack, for
`Artifacts/Ed448PublicKey/X86.lean` and `Artifacts/Ed448SignCached/X86.lean`.
Like `Facts.lean`, only registration files import this module.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG.X86

/-- `vg_ed448_scalar_base` meets what its callers take of it. -/
theorem scalarBase_calleeOk : CalleeOk scalarBaseLocal Impl.Ed448.X86.scalarBase :=
  ⟨scalarBase_ok Proof.Ed448.baseComb_ok, scalarBase_ct,
    NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ed448.X86
