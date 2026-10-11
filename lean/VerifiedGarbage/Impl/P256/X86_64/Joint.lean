module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64

/-! The measured x86-64 P-256 joint multiplication layout and doubling dispatch. -/

@[expose] public section

namespace VG.Impl.P256.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

def publicJoint : Joint.Cfg :=
  ⟨p256.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    6000,"VG_P256_COMB",4000,5408⟩

def publicJointAdx : Joint.Cfg :=
  {publicJoint with K := p256x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP}

/-- The joint loop's doubler: in place, with a modular halving. -/
def jointDouble (K : WinCfg) : Prog isa := doubleHalfPublic K.M K.S K.R

end VG.Impl.P256.X86_64
