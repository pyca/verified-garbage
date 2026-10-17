module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Sm3.X86_64
meta import VerifiedGarbage.Impl.Sm3.X86_64

/-!
# SM3 on x86-64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sm3.X86_64.compress

end VG
