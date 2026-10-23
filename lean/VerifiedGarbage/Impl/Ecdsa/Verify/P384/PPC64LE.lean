module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE

/-! # `vg_ecdsa_p384_verify` on PPC64LE -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa := Cfg.verify Impl.Ecdsa.PPC64LE.p384

end VG.Impl.Ecdsa.Verify.PPC64LE
