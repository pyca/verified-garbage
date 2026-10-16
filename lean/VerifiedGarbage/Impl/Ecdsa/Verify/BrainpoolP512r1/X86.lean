module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86

/-! # ECDSA verification over brainpoolP512r1 on x86 (32-bit): eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_brainpoolp512r1_verify`. -/
def verifyBrainpoolP512r1 : Prog isa := Cfg.verify Impl.Ecdsa.X86.brainpoolp512r1

end VG.Impl.Ecdsa.Verify.X86
