module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.ChaCha20.X86.Xor
meta import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# ChaCha20 on X86: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.X86.block
materialize_code Impl.ChaCha20.X86.Xor.xor
materialize_code Impl.ChaCha20.X86.Xor.xorSsse3

end VG
