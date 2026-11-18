module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Impl.Ecdsa.P224.X86Comb

/-! # ECDSA verification over P-224 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_p224_verify`. -/
def verifyP224 : Prog isa := Cfg.verifyComb Impl.Ecdsa.X86.p224Comb

end VG.Impl.Ecdsa.Verify.X86
