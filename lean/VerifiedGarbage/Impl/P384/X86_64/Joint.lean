module

public import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint

/-! The x86-64 P-384 joint multiplication layout, for public verification. -/

@[expose] public section

namespace VG.Impl.P384.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- P-384 for verification: `p384` with `pubVerify` (`n < p ≤ 2n`), whose
final check compares `x mod n` with `r` in projective coordinates. Signing
and ECDH, which never read `pubVerify`, keep `p384`. -/
def p384v : Cfg := { p384 with pubVerify := true }

/-- `p384v` multiplying with BMI2 and ADX. -/
def p384vx : Cfg := { p384x with pubVerify := true }

/-- The joint loop's working space, past the window method's table (from
`5392`): the cached `Z²`, `Z³` of its eight entries at `5392`, the selected
pair at `6160`, and the generator's digits at `6400`. -/
def publicJoint : Joint.Cfg :=
  ⟨p384v.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    6400,"VG_P384_COMB",5392,6160,some Spec.Weierstrass.PointOps.p384,false,false⟩

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
