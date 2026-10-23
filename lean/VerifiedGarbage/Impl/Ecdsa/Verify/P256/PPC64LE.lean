module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE

/-! # `vg_ecdsa_p256_verify` on PPC64LE -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `vg_ecdsa_p256_verify`. -/
def verifyP256 : Prog isa := Cfg.verify Impl.Ecdsa.PPC64LE.p256

end VG.Impl.Ecdsa.Verify.PPC64LE
