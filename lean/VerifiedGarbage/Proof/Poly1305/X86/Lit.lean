module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Poly1305.X86
meta import VerifiedGarbage.Impl.Poly1305.X86
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# Poly1305 on X86: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Poly1305.X86.init
materialize_code Impl.Poly1305.X86.blocks
materialize_code Impl.Poly1305.X86.update
materialize_code Impl.Poly1305.X86.finalize

end VG
