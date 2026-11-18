module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86Comb

/-! # ECDSA verification over secp256k1 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_secp256k1_verify`. -/
def verifySecp256k1 : Prog isa := Cfg.verifyComb Impl.Ecdsa.X86.secp256k1Comb

end VG.Impl.Ecdsa.Verify.X86
