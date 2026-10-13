module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86

/-! # ECDSA verification over brainpoolP384r1 on x86 (32-bit): six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_brainpoolp384r1_verify`. -/
def verifyBrainpoolP384r1 : Prog isa := Cfg.verify Impl.Ecdsa.X86.brainpoolp384r1

end VG.Impl.Ecdsa.Verify.X86
