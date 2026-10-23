module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE

/-! # ECDH over brainpoolP384r1 on PPC64LE: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_brainpoolp384r1`. -/
def exchangeBrainpoolP384r1 : Prog isa := Cfg.exchange Impl.Ecdsa.PPC64LE.brainpoolp384r1

end VG.Impl.Ecdh.PPC64LE
