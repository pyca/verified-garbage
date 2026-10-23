module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE

/-! # ECDH over secp256k1 on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_secp256k1`. -/
def exchangeSecp256k1 : Prog isa := Cfg.exchange Impl.Ecdsa.PPC64LE.secp256k1

end VG.Impl.Ecdh.PPC64LE
