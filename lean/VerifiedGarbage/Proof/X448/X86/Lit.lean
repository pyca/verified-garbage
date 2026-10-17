module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.X448.X86.FnLit
meta import VerifiedGarbage.Proof.X448.X86.FnLit
public import VerifiedGarbage.Impl.X448.X86
meta import VerifiedGarbage.Impl.X448.X86
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# X448 on x86 (32-bit): the code as a literal

The field arithmetic is fully unrolled: the literal of the code
(`materialize_code`, `Proof/Framework/Lit.lean`) spares the kernel building
the instructions again in every check that evaluates the code (constant time,
`spSafe`).
-/

@[expose] public section

namespace VG.Impl.X448.X86

materialize_code x448

end VG.Impl.X448.X86
