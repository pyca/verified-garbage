module

public import VerifiedGarbage.Impl.Scrypt.PPC64LE.RoMix
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Scrypt.PPC64LE.RoMix
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
# scrypt on PPC64LE: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Scrypt.PPC64LE.salsa
materialize_code Impl.Scrypt.PPC64LE.blockMix
materialize_code Impl.Scrypt.PPC64LE.roMix

end VG
