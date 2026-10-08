import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64

/-! # secp256k1 on x86-64 -/

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

def exchangeSecp256k1 : Prog isa := Cfg.exchange Ecdsa.X86_64.secp256k1

end VG.Impl.Ecdh.X86_64
