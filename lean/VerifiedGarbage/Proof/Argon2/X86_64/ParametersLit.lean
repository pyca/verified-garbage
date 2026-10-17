module

public import VerifiedGarbage.Impl.Argon2.X86_64.Parameters
meta import VerifiedGarbage.Impl.Argon2.X86_64.Parameters
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! Checked literal of rounded-memory parameter computation. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.X86_64.Parameters.code

end VG
