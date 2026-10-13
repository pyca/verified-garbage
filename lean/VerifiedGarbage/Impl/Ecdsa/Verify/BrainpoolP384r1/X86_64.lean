module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64

/-! # brainpoolP384r1 on x86-64 -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64

def verifyBrainpoolP384r1 : Prog isa := Cfg.verify Ecdsa.X86_64.brainpoolp384r1

end VG.Impl.Ecdsa.Verify.X86_64
