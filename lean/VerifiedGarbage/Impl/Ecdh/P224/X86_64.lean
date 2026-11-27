module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P224.X86_64

/-! # ECDH over P-224 on x86-64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `vg_ecdh_p224`. -/
def exchangeP224 : Prog isa := Cfg.exchange Impl.Ecdsa.X86_64.p224

end VG.Impl.Ecdh.X86_64

namespace VG.Impl.Ecdh.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_ecdh_p224` as emitted: its code, then its cleanup. -/
def exchangeP224 : Prog isa := scrubAll .sse 32 8 _root_.VG.Impl.Ecdh.X86_64.exchangeP224

end VG.Impl.Ecdh.X86_64.Fn
