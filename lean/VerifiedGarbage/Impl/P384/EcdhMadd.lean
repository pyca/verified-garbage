module

public import VerifiedGarbage.Impl.P384.EcdhDouble

/-!
# P-384's mixed addition for ECDH's window on AArch64

`madd` is the window's mixed addition `D = R + E` (`maddJ`, 8 products and
3 squares) in a straight line, each field operation `Ops.op`'s, in place of
the calls to `vg_p384_mul_mod_p` and `vg_p384_sqr_mod_p` the field program
(`fprogB`) makes. It uses the registers `x1`–`x17` and `x21`–`x25`, which
ECDH saves on entry.
-/

@[expose] public section

namespace VG.Impl.P384.EcdhMadd
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.P384.EcdhDouble

/-- `D = R + E` in Jacobian coordinates, for an affine `E`. -/
def madd : List Instr := (maddJ K.S K.R K.E K.D).flatMap Ops.op

end VG.Impl.P384.EcdhMadd
