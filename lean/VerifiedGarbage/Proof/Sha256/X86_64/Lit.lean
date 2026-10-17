module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Sha256.X86_64
meta import VerifiedGarbage.Impl.Sha256.X86_64

/-!
# SHA-256 on X86_64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha256.X86_64.compress

end VG
