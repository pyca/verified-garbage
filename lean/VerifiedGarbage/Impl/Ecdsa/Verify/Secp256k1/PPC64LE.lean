module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE

/-! # `vg_ecdsa_secp256k1_verify` on PPC64LE -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `vg_ecdsa_secp256k1_verify`. -/
def verifySecp256k1 : Prog isa := Cfg.verify Impl.Ecdsa.PPC64LE.secp256k1

end VG.Impl.Ecdsa.Verify.PPC64LE
