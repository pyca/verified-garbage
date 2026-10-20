module

public import VerifiedGarbage.Impl.Sha256.AArch64.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha256.AArch64.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SHA-256 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha256.AArch64.compress
materialize_code Impl.Sha256.AArch64.Stream.update
materialize_code Impl.Sha256.AArch64.Stream.finalize

end VG
