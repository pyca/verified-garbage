module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86

/-! # ECDSA verification over brainpoolP256r1 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_brainpoolp256r1_verify`. -/
def verifyBrainpoolP256r1 : Prog isa := Cfg.verify Impl.Ecdsa.X86.brainpoolp256r1

end VG.Impl.Ecdsa.Verify.X86
