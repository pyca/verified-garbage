module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE

/-! # `vg_ecdsa_p224_verify` on PPC64LE -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `vg_ecdsa_p224_verify`. -/
def verifyP224 : Prog isa := Cfg.verify Impl.Ecdsa.PPC64LE.p224

end VG.Impl.Ecdsa.Verify.PPC64LE
