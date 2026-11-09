module

public import VerifiedGarbage.Impl.P256.VerifyArithmetic
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.P256.VerifyArithmetic

def original (k : Kind) := fprog VG.Impl.P256.VerifyDouble.M (operations k)
def optimized (k : Kind) := VG.Impl.Weierstrass.AArch64.Forward.optimize (original k)

end VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
