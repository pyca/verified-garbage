module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.MulAdd
meta import VerifiedGarbage.Impl.Ed25519.X86.MulAdd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG.Impl.Ed25519.X86
materialize_code scalarMulAdd
end VG.Impl.Ed25519.X86
