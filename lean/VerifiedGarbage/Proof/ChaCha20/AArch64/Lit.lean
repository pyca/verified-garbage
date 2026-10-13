module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.AArch64.block
materialize_code Impl.ChaCha20.AArch64.Xor.xor

end VG
