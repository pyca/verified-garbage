module

import VerifiedGarbage.Proof.Ed448.X86.VerifyCT
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Ed448.X86.VerifyLocal
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 verification's equation on x86 (32-bit): `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqOk`, which the registration
file passes in, from `Proof/Ed448/Facts.lean`), constant time
(`VerifyCT.lean`), and a concrete state satisfying the signature's contract,
with the 20 bytes of stack below the return address that the calls of the
field functions use. The contract lets timing depend on the inputs; the
code's depends on the pointers alone. The local contract only reads the
arguments; the shared one lets the code write them too (`writeArgs`), which
it does not (`Verified.narrowTo`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (RecoverOk VerifyEqOk)
open VG.Impl.Ed448.X86 (verifyEquation)

theorem verifyEquation_ok (hR : RecoverOk) (hE : VerifyEqOk) (s : State) (h : verifyEquationLocal.pre s) :
    ∃ tr t, Exec isa verifyEquation s tr t ∧ abiPreserved s t ∧ verifyEquationLocal.post s t := by
  obtain ⟨tr, t, he, h1, h2⟩ := verifyEquation_main hR hE (VerifyPre.of h)
  exact ⟨tr, t, he, h1, h2⟩

end VG.Proof.Ed448.X86
