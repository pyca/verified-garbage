module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64

/-! The measured x86-64 P-256 joint multiplication layout and doubling dispatch. -/

@[expose] public section

namespace VG.Impl.P256.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- The top digit peeled: its first iteration in the loop measured 0.25%
slower on an Intel Xeon 8370C. The table of `Q`'s odd multiples by co-Z
arithmetic (`coZ`): verification 1.6% faster on an Intel Xeon (Ice Lake). -/
def publicJoint : Joint.Cfg :=
  { K := p256.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    gBits := 6000, tsym := "VG_P256_COMB", cache := 4000, selected := 5408, peel := true,
    coZ := true }

def publicJointAdx : Joint.Cfg :=
  {publicJoint with K := p256x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP}

/-- The joint loop's doubler: in place, with a modular halving. -/
def jointDouble (K : WinCfg) : Prog isa := doubleHalfPublic K.M K.S K.R

end VG.Impl.P256.X86_64
