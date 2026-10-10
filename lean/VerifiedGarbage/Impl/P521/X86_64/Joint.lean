import VerifiedGarbage.Impl.Weierstrass.X86_64.JointDouble
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
import VerifiedGarbage.Impl.Ecdh.X86_64

/-! The x86-64 P-521 joint multiplication layout, for public verification. -/
namespace VG.Impl.P521.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- The joint loop's working space, where the window method works but the
joint method does not: the generator's digits at `3304`, the cached `Z²`,
`Z³` of the eight entries at `4096` (past the products' temporary area,
`Mont.fnTmp`), and the selected pair at `5968`, between the window method's
bits of `k` and its table of odd multiples. `p521` already has `pubVerify`. -/
def publicJoint : Joint.Cfg :=
  ⟨p521.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    3304,"VG_P521_COMB",4096,5968⟩

def publicJointAdx : Joint.Cfg :=
  {publicJoint with K := p521x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP}

end VG.Impl.P521.X86_64
