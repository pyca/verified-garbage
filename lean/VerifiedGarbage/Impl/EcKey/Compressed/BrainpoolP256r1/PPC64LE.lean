module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LE

/-! # SEC 1 point conversion over brainpoolP256r1 on PPC64LE: four-word field elements -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE

/-- `vg_ec_brainpoolp256r1_compress_public_key`. -/
def compressBrainpoolP256r1 : Prog isa := compress Impl.Ecdsa.PPC64LE.brainpoolp256r1

end VG.Impl.EcKey.Compressed.PPC64LE
