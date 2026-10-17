module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite
meta import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite

/-! A checked literal for the block write after compression. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.X86_64.FillWrite.code

end VG
