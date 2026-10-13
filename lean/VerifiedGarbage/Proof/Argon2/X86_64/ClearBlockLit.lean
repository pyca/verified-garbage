module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Argon2.X86_64.ClearBlock
meta import VerifiedGarbage.Impl.Argon2.X86_64.ClearBlock
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Checked literal of a complete address-generation block clear. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.X86_64.ClearBlock.code

end VG
