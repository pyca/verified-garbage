module

public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86_64

/-! # brainpoolP320r1 on x86-64 -/

@[expose] public section

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

def exchangeBrainpoolP320r1 : Prog isa := Cfg.exchange Ecdsa.X86_64.brainpoolp320r1

end VG.Impl.Ecdh.X86_64
