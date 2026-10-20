module

public import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Checked literals for the public dimension setup blocks -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.X86_64.MemoryInit.clearSetupCode
materialize_code Impl.Argon2.X86_64.MemoryInit.lanesSetupCode

end VG
