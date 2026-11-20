module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.EcKey.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P192.X86_64

/-! # p192 on x86-64 -/

@[expose] public section

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

def publicKeyP192 : Prog isa := Cfg.publicKey Ecdsa.X86_64.p192

end VG.Impl.EcKey.X86_64

namespace VG.Impl.EcKey.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_ec_p192_public_key` as emitted: its code, then its cleanup. -/
def publicKeyP192 : Prog isa := scrubAll .sse 32 8 _root_.VG.Impl.EcKey.X86_64.publicKeyP192

end VG.Impl.EcKey.X86_64.Fn
