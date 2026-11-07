module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeK
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeK
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := Arithmetic.original .jacHead
def optimized := Arithmetic.optimized .jacHead
materialize_value leftCode := original
forward_state rightCode.lit := optimized
theorem rightCode.lit_eq : optimized=rightCode.lit := optimize_of_lit leftCode.lit_eq (by kernel_rfl)
end VG.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
