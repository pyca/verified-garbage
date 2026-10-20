module

public import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# scrypt on Arm: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Scrypt.Arm.salsa
materialize_code Impl.Scrypt.Arm.blockMix
materialize_code Impl.Scrypt.Arm.roMix

end VG
