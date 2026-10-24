module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE

/-! # SEC 1 point conversion over P-521 on PPC64LE: nine-word field elements -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE

/-- `vg_ec_p521_compress_public_key`. -/
def compressP521 : Prog isa := compress Impl.Ecdsa.PPC64LE.p521

/-- `vg_ec_p521_decompress_public_key`. -/
def decompressP521 : Prog isa := decompress Impl.Ecdsa.PPC64LE.p521

end VG.Impl.EcKey.Compressed.PPC64LE
