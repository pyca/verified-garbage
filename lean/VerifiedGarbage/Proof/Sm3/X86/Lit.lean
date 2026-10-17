module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Sm3.X86.Stream
meta import VerifiedGarbage.Impl.Sm3.X86.Stream
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# SM3 on x86: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sm3.X86.compress
materialize_code Impl.Sm3.X86.Stream.update
materialize_code Impl.Sm3.X86.Stream.finalize

end VG
