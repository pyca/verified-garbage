module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Argon2.X86_64.FillPointers
meta import VerifiedGarbage.Impl.Argon2.X86_64.FillPointers
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Checked literal of the complete filling pointer setup. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.X86_64.FillPointers.code

end VG
