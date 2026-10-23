module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LE

/-! # ECDH over brainpoolP256r1 on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_brainpoolp256r1`. -/
def exchangeBrainpoolP256r1 : Prog isa := Cfg.exchange Impl.Ecdsa.PPC64LE.brainpoolp256r1

end VG.Impl.Ecdh.PPC64LE
