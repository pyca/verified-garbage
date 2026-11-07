module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.CombGeneral
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64

/-! # brainpoolP512r1 on x86-64

Verification computes `[u]G` by the signature's comb (`Cfg.verifyG`, from
`VG_BRAINPOOLP512R1_COMB`) and `[v]Q` by the ladder. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64

def verifyBrainpoolP512r1 : Prog isa :=
  Cfg.verifyG Ecdsa.X86_64.brainpoolp512r1S Ecdsa.X86_64.brainpoolp512r1Comb

end VG.Impl.Ecdsa.Verify.X86_64
