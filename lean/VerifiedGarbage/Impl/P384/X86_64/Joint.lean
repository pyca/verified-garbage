import VerifiedGarbage.Impl.Weierstrass.X86_64.JointDouble
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Impl.Ecdh.X86_64

/-! The x86-64 P-384 joint multiplication layout, for public verification. -/
namespace VG.Impl.P384.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- P-384 for verification: `p384` with `pubVerify` (`n < p ≤ 2n`), whose
final check compares `x mod n` with `r` in projective coordinates. Signing
and ECDH, which never read `pubVerify`, keep `p384`. -/
def p384v : Cfg := { p384 with pubVerify := true }

/-- `p384v` multiplying with BMI2 and ADX. -/
def p384vx : Cfg := { p384x with pubVerify := true }

/-- The joint loop's working space, past the window method's table (from
`5344`): the cached `Z²`, `Z³` of its eight entries at `5376`, the selected
pair at `6144`, and the generator's digits at `6400`. -/
def publicJoint : Joint.Cfg :=
  ⟨p384v.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    6400,"VG_P384_COMB",5376,6144⟩

def publicJointAdx : Joint.Cfg :=
  {publicJoint with K := p384vx.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP}

end VG.Impl.P384.X86_64
