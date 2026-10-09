import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Impl.Ecdsa.P192.X86_64

/-! # p192 on x86-64 -/

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

def exchangeP192 : Prog isa := Cfg.exchange Ecdsa.X86_64.p192

end VG.Impl.Ecdh.X86_64
