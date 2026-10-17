module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Argon2.X86_64.FillPointers
meta import VerifiedGarbage.Impl.Argon2.X86_64.FillPointers

/-! Checked literal of the complete filling pointer setup. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.X86_64.FillPointers.code

end VG
