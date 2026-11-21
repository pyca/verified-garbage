module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64

/-! # secp256k1 on x86-64 -/

@[expose] public section

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

def exchangeSecp256k1 : Prog isa := Cfg.exchange Ecdsa.X86_64.secp256k1

end VG.Impl.Ecdh.X86_64

namespace VG.Impl.Ecdh.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_ecdh_secp256k1` as emitted: its code, then its cleanup. -/
def exchangeSecp256k1 : Prog isa := scrubAll .sse 32 8 _root_.VG.Impl.Ecdh.X86_64.exchangeSecp256k1

end VG.Impl.Ecdh.X86_64.Fn
