module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Sha3.X86
meta import VerifiedGarbage.Impl.Sha3.X86
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# Keccak-f[1600] on x86 (32-bit): the code as a literal

The permutation's code is built by functions (its rounds, planes and
round-constant stores): its literal (`materialize_code`) spares the kernel
building the instructions in every check that evaluates the code (constant
time, `NoSp`, the stack's use, `spSafe`), and the streaming functions call it.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86

materialize_code permute

end VG.Impl.Sha3.X86
