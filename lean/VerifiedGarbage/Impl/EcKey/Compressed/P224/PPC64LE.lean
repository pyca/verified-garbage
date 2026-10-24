module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE

/-! # SEC 1 point conversion over P-224 on PPC64LE: four-word field elements -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE

/-- `vg_ec_p224_compress_public_key`. -/
def compressP224 : Prog isa := compress Impl.Ecdsa.PPC64LE.p224

/-- `vg_ec_p224_decompress_public_key`. -/
def decompressP224 : Prog isa := decompress Impl.Ecdsa.PPC64LE.p224

end VG.Impl.EcKey.Compressed.PPC64LE
