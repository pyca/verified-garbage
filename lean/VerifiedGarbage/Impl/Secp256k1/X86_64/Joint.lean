module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
public import VerifiedGarbage.Impl.Secp256k1.GTable9
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint

/-! The x86-64 secp256k1 joint multiplication layout, for public verification. -/

@[expose] public section

namespace VG.Impl.Secp256k1.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- The verifier's table of `[m]G`, `m = 1 … 256`, which its generator digits
of width nine index, in the static `VG_SECP256K1_GTAB`. -/
def secp256k1GTab : CombData :=
  { w := 9, tbl := Impl.Secp256k1.secp256k1G9, start := Impl.Secp256k1.secp256k1G9Start,
    tsym := "VG_SECP256K1_GTAB" }

/-- secp256k1 for verification: `secp256k1` with `pubVerify` (`n < p ≤ 2n`),
whose final check compares `x mod n` with `r` in projective coordinates, and
with the table of its generator digits (`gtab`). Signing and ECDH, which
never read either, keep `secp256k1`. -/
def secp256k1v : Cfg := { secp256k1 with pubVerify := true, gtab := some secp256k1GTab }

/-- The joint loop's working space, P-256's on four words: the cached `Z²`,
`Z³` of the eight entries at `4000`, the selected pair at `5408`, and the
generator's digits of width nine (`gw`), in sixteen bits each, at `6000`.
The digits' additions are calls (`pts`), and they and the table of `Q`'s odd
multiples double equal points for `a = 0` (`dblJ0`). -/
def publicJoint : Joint.Cfg :=
  { K := secp256k1v.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    gBits := 6000, tsym := "VG_SECP256K1_GTAB", cache := 4000, selected := 5408,
    pts := some Impl.Weierstrass.PointOps.secp256k1, gw := 9, dbl := dblJ0 }

/-- The joint loop's doubler: a call of `vg_secp256k1_jac_double`. -/
def jointDouble (K : WinCfg) : Prog isa := PointOps.doubleCall Impl.Weierstrass.PointOps.secp256k1 K dblJ0

end VG.Impl.Secp256k1.X86_64
