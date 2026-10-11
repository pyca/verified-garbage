module

public import VerifiedGarbage.Impl.EcKey.X86_64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64

/-! # secp256k1 on x86-64 -/

@[expose] public section

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

def publicKeySecp256k1 : Prog isa := Cfg.publicKey Ecdsa.X86_64.secp256k1

end VG.Impl.EcKey.X86_64
