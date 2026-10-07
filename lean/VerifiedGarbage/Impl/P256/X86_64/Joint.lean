import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64

/-! The measured x86-64 P-256 joint multiplication layout and doubling dispatch. -/
namespace VG.Impl.P256.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

def publicJoint : Joint.Cfg :=
  ⟨p256.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    6000,"VG_P256_COMB",4000,5408⟩

def publicJointAdx : Joint.Cfg :=
  {publicJoint with K := p256x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP}

def jointWindow (c : Joint.Cfg) : Prog isa :=
  Joint.window c (doubleHalfPublic c.K.M c.K.S c.K.R)

end VG.Impl.P256.X86_64
