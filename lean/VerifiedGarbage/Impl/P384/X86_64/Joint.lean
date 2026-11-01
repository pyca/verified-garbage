module

public import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
public import VerifiedGarbage.Impl.P384.GTable9
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint

/-! The x86-64 P-384 joint multiplication layout, for public verification. -/

@[expose] public section

namespace VG.Impl.P384.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- The verifier's table of `[m]G`, `m = 1 … 256`, which its generator digits
of width nine index, in the static `VG_P384_GTAB`. -/
def p384GTab : CombData :=
  { w := 9, tbl := Impl.P384.p384G9, start := Impl.P384.p384G9Start, tsym := "VG_P384_GTAB" }

/-- P-384 for verification: `p384` with `pubVerify` (`n < p ≤ 2n`), whose
final check compares `x mod n` with `r` in projective coordinates, and with
the table of its generator digits (`gtab`) in place of the comb, which only
signing and key generation run. Signing and ECDH keep `p384`. -/
def p384v : Cfg := { p384 with pubVerify := true, comb := none, gtab := some p384GTab }

/-- `p384v` multiplying with BMI2 and ADX. -/
def p384vx : Cfg := { p384x with pubVerify := true, comb := none, gtab := some p384GTab }

/-- The joint loop's working space, past the window method's table (from
`5392`): the cached `Z²`, `Z³` of its eight entries at `5392`, the selected
pair at `6160`, and the generator's digits at `6400`. The table of `Q`'s odd
multiples by co-Z arithmetic (`coZ`): verification 1.3% faster on an Intel
Xeon (Ice Lake). The generator's digits of width nine (`gw`), in sixteen bits
each at `6400`, from the table `p384GTab`. -/
def publicJoint : Joint.Cfg :=
  { K := p384v.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    gBits := 6400, tsym := "VG_P384_GTAB", cache := 5392, selected := 6160,
    pts := some Impl.Weierstrass.PointOps.p384, coZ := true, gw := 9 }

/-- `publicJoint` with BMI2 and ADX. -/
def publicJointAdx : Joint.Cfg :=
  {publicJoint with K := p384vx.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP}

/-- The joint loop's doubler: in place (`doubleIn`), with no copy from a
temporary point. -/
def jointDouble (K : WinCfg) : Prog isa := doubleIn K.M K.S K.R

/-- The joint loop's doubler with BMI2 and ADX: in place, with its small
multiples fused (`doubleCms`), as in ECDH. -/
def jointDoubleAdx (K : WinCfg) : Prog isa := doubleCms K.M K.S K.R

end VG.Impl.P384.X86_64
