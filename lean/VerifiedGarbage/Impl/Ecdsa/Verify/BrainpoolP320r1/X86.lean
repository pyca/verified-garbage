module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86Comb

/-! # ECDSA verification over brainpoolP320r1 on x86 (32-bit): five-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_brainpoolp320r1_verify`. -/
def verifyBrainpoolP320r1 : Prog isa := Cfg.verifyComb Impl.Ecdsa.X86.brainpoolp320r1Comb

end VG.Impl.Ecdsa.Verify.X86
