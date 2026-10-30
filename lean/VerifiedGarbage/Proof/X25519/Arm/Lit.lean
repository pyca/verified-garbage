module

public import VerifiedGarbage.Impl.X25519.Arm
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.X25519.Arm
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# X25519 on 32-bit ARM: the code as a literal

The code of `vg_x25519` and `vg_x25519_umaal` as literals (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG

materialize_code Impl.X25519.Arm.x25519
materialize_code Impl.X25519.Arm.x25519Umaal

end VG
