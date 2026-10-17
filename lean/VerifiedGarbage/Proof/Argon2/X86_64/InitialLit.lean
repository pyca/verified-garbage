module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Argon2.X86_64.Initial
meta import VerifiedGarbage.Impl.Argon2.X86_64.Initial

/-! A checked literal for the six-word H₀ header. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.X86_64.Initial.headerCode

end VG
