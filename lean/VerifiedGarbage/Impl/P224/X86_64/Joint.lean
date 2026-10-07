import VerifiedGarbage.Impl.Weierstrass.X86_64.JointDouble
import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
import VerifiedGarbage.Impl.Ecdh.X86_64

/-! The x86-64 P-224 joint multiplication layout, for public verification. -/
namespace VG.Impl.P224.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- P-224 for verification: `p224` with `pubVerify` (`n < p ≤ 2n`), whose
final check compares `x mod n` with `r` in projective coordinates. Signing
and ECDH, which never read `pubVerify`, keep `p224`. -/
def p224v : Cfg := { p224 with pubVerify := true }

/-- The joint loop's working space, P-256's on four words: the cached `Z²`,
`Z³` of the eight entries at `4000`, the selected pair at `5408`, and the
generator's digits at `6000`. -/
def publicJoint : Joint.Cfg :=
  ⟨p224v.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    6000,"VG_P224_COMB",4000,5408⟩

end VG.Impl.P224.X86_64
