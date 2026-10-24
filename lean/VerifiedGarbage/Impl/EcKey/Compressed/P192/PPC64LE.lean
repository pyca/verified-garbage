module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE

/-! # SEC 1 point conversion over P-192 on PPC64LE: three-word field elements -/

@[expose] public section

namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE

/-- `vg_ec_p192_compress_public_key`. -/
def compressP192 : Prog isa := compress Impl.Ecdsa.PPC64LE.p192

end VG.Impl.EcKey.Compressed.PPC64LE
