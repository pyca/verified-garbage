module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# ChaCha20 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.AArch64.block
materialize_code Impl.ChaCha20.AArch64.Xor.xor

end VG
