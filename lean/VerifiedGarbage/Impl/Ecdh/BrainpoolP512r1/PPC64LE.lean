module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE

/-! # ECDH over brainpoolP512r1 on PPC64LE: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_brainpoolp512r1`. -/
def exchangeBrainpoolP512r1 : Prog isa := Cfg.exchange Impl.Ecdsa.PPC64LE.brainpoolp512r1

end VG.Impl.Ecdh.PPC64LE
