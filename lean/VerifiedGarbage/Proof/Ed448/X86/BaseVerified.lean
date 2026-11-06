module
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
public import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Framework.X86.Inline

import VerifiedGarbage.Proof.Ed448.X86.BaseCT
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 base-point multiplication on x86 (32-bit): `Verified`

Correctness (`BaseMain.lean`), constant time (`BaseCT.lean`),
satisfiability, and the shared contract of `Spec/` with the 20 bytes of stack
below the return address that the calls of the field functions use, given that the ladder the
code computes encodes as `[k]B` (`Proof.Ed448.BaseLadderOk`, proven with the
group law in `Proof/Ed448/Facts.lean`, which only the registration file
imports). The local contract only reads the arguments; the shared one lets
the code write them too (`writeArgs`), which it does not
(`Verified.narrowTo`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (BaseLadderOk decodeLE_below)
open VG.Impl.Ed448.X86 (scalarBase)

theorem scalarBase_ok (hl : BaseLadderOk) (s : State) (h : scalarBaseLocal.pre s) :
    ∃ tr t, Exec isa scalarBase s tr t ∧ abiPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨tr, t, he, h1, h2⟩ := scalarBase_ladder (BasePre.of h)
  refine ⟨tr, t, he, h1, ?_⟩
  change Spec.Ed448.bytesAt t.mem _ 57 =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul _ Spec.Ed448.basePoint)
  rw [h2, hl _ (decodeLE_below (by simp [Spec.Ed448.bytesAt]))]

end VG.Proof.Ed448.X86
