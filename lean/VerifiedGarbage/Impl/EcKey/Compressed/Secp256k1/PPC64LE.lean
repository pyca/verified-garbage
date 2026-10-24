module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE

/-! # SEC 1 point conversion over secp256k1 on PPC64LE: four-word field elements -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE

/-- `vg_ec_secp256k1_compress_public_key`. -/
def compressSecp256k1 : Prog isa := compress Impl.Ecdsa.PPC64LE.secp256k1

end VG.Impl.EcKey.Compressed.PPC64LE
