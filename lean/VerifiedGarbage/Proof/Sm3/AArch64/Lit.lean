module

public import VerifiedGarbage.Impl.Sm3.AArch64.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm3.AArch64.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SM3 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sm3.AArch64.compress
materialize_code Impl.Sm3.AArch64.Stream.update
materialize_code Impl.Sm3.AArch64.Stream.finalize

end VG
