module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round
meta import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

@[expose] public section

namespace VG

materialize_value Impl.CmacTripleDes.Arm.roundKeys

theorem Proof.CmacTripleDes.Arm.roundKeys_eq :
    Impl.CmacTripleDes.Arm.roundKeys = Impl.CmacTripleDes.Arm.roundKeys.lit :=
  Impl.CmacTripleDes.Arm.roundKeys.lit_eq

end VG
