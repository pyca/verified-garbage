module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE

/-! # SEC 1 point conversion over P-384 on PPC64LE: six-word field elements -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE

/-- `vg_ec_p384_compress_public_key`. -/
def compressP384 : Prog isa := compress Impl.Ecdsa.PPC64LE.p384

/-- `vg_ec_p384_decompress_public_key`. -/
def decompressP384 : Prog isa := decompress Impl.Ecdsa.PPC64LE.p384

end VG.Impl.EcKey.Compressed.PPC64LE
