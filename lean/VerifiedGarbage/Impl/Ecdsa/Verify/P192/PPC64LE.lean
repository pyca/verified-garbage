module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE

/-! # `vg_ecdsa_p192_verify` on PPC64LE -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `vg_ecdsa_p192_verify`. -/
def verifyP192 : Prog isa := Cfg.verify Impl.Ecdsa.PPC64LE.p192

end VG.Impl.Ecdsa.Verify.PPC64LE
