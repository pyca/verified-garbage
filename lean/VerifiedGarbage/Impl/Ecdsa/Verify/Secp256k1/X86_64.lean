module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64

/-! # secp256k1 on x86-64 -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64

def verifySecp256k1 : Prog isa := Cfg.verify Ecdsa.X86_64.secp256k1

end VG.Impl.Ecdsa.Verify.X86_64
