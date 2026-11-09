module

public import VerifiedGarbage.Proof.P256.EcdhJac.FieldCase
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeK
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.P256.EcdhJac.FieldCase
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeK
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.P256.EcdhJac.Dblu
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := fprog VG.Impl.P256.EcdhJac.K.M VG.Impl.P256.EcdhJac.dbluOps
def optimized := VG.Impl.Weierstrass.AArch64.Forward.optimize original
materialize_value leftCode := original
forward_state rightCode.lit := optimized

end VG.Proof.P256.EcdhJac.Dblu
