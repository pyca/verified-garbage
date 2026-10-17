module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Sha512.AArch64
meta import VerifiedGarbage.Impl.Sha512.AArch64

/-!
# SHA-512 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha512.AArch64.compress

end VG
