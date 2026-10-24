module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE

/-! # SEC 1 point conversion over P-256 on PPC64LE: four-word field elements -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE

/-- `vg_ec_p256_compress_public_key`. -/
def compressP256 : Prog isa := compress Impl.Ecdsa.PPC64LE.p256

end VG.Impl.EcKey.Compressed.PPC64LE
