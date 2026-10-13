module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P192.X86_64

/-! # p192 on x86-64 -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64

def verifyP192 : Prog isa := Cfg.verify Ecdsa.X86_64.p192

end VG.Impl.Ecdsa.Verify.X86_64
