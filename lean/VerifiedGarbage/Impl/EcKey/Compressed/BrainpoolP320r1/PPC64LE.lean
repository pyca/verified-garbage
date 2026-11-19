module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.PPC64LE

/-! # SEC 1 point conversion over brainpoolP320r1 on PPC64LE: five-word field elements -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE

/-- `vg_ec_brainpoolp320r1_compress_public_key`. -/
def compressBrainpoolP320r1 : Prog isa := compress Impl.Ecdsa.PPC64LE.brainpoolp320r1

/-- `vg_ec_brainpoolp320r1_decompress_public_key`. -/
def decompressBrainpoolP320r1 : Prog isa := decompress Impl.Ecdsa.PPC64LE.brainpoolp320r1

end VG.Impl.EcKey.Compressed.PPC64LE
