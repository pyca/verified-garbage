module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Sm4.X86.Ctr
meta import VerifiedGarbage.Impl.Sm4.X86.Ctr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! # SM4-CTR on x86: a code literal for the taint and stack checks -/

@[expose] public section

namespace VG.Proof.Sm4.X86

materialize_flat_code ctrCode := Impl.Sm4.X86.ctr

end VG.Proof.Sm4.X86
