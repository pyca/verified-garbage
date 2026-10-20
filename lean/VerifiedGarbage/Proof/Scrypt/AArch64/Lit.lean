module

public import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# scrypt on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Scrypt.AArch64.salsa
materialize_code Impl.Scrypt.AArch64.blockMix
materialize_code Impl.Scrypt.AArch64.roMix

end VG
