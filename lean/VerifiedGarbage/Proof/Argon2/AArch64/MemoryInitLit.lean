module

public import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
meta import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Checked literals for the public dimension setup blocks -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.AArch64.MemoryInit.clearSetupCode
materialize_code Impl.Argon2.AArch64.MemoryInit.lanesSetupCode

end VG
