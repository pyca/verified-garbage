module

public import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
meta import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Checked literals for the public dimension setup blocks -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.AArch64.MemoryInit.clearSetupCode
materialize_code Impl.Argon2.AArch64.MemoryInit.lanesSetupCode

end VG
