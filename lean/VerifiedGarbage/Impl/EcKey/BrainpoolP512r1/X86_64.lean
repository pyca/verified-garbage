module

public import VerifiedGarbage.Impl.EcKey.X86_64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64

/-! # brainpoolP512r1 on x86-64 -/

@[expose] public section

namespace VG.Impl.EcKey.X86_64

open VG.X86_64

def publicKeyBrainpoolP512r1 : Prog isa := Cfg.publicKey Ecdsa.X86_64.brainpoolp512r1

end VG.Impl.EcKey.X86_64
