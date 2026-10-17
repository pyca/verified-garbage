module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Sm3.AArch64.Stream
meta import VerifiedGarbage.Impl.Sm3.AArch64.Stream

/-!
# SM3 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sm3.AArch64.compress
materialize_code Impl.Sm3.AArch64.Stream.update
materialize_code Impl.Sm3.AArch64.Stream.finalize

end VG
