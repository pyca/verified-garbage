module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.ChaCha20.X86.Xor
meta import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20 on X86: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.X86.block
materialize_code Impl.ChaCha20.X86.Xor.xor
materialize_code Impl.ChaCha20.X86.Xor.xorSsse3

end VG
