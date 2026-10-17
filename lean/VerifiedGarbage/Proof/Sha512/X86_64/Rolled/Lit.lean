module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Sha512.X86_64.Rolled
meta import VerifiedGarbage.Impl.Sha512.X86_64.Rolled

/-!
# SHA-512 on x86-64, rolled: the code as a literal
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha512.X86_64.Rolled.compress

end VG
