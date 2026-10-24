module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE

/-! # `vg_ecdsa_p521_verify` on PPC64LE -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa := Cfg.verify Impl.Ecdsa.PPC64LE.p521

end VG.Impl.Ecdsa.Verify.PPC64LE
