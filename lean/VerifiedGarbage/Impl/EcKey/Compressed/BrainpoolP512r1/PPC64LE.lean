module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE

/-! # SEC 1 point conversion over brainpoolP512r1 on PPC64LE: eight-word field elements -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE

/-- `vg_ec_brainpoolp512r1_compress_public_key`. -/
def compressBrainpoolP512r1 : Prog isa := compress Impl.Ecdsa.PPC64LE.brainpoolp512r1

/-- `vg_ec_brainpoolp512r1_decompress_public_key`. -/
def decompressBrainpoolP512r1 : Prog isa := decompress Impl.Ecdsa.PPC64LE.brainpoolp512r1

end VG.Impl.EcKey.Compressed.PPC64LE
