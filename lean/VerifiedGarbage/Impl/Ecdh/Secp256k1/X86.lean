module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86

/-! # ECDH over secp256k1 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_secp256k1`. -/
def exchangeSecp256k1 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.secp256k1

end VG.Impl.Ecdh.X86
