module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Round
meta import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Round
public import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

@[expose] public section

namespace VG

materialize_value Impl.CmacTripleDes.X86_64.roundKeys

theorem Proof.CmacTripleDes.X86_64.roundKeys_eq :
    Impl.CmacTripleDes.X86_64.roundKeys = Impl.CmacTripleDes.X86_64.roundKeys.lit :=
  Impl.CmacTripleDes.X86_64.roundKeys.lit_eq

end VG
