module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.WindowA

/-! # ECDH over brainpoolP256r1 on PPC64LE: four-word field elements and scalars, `[d]P` by windows -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_brainpoolp256r1`: `[d]P` by four-bit windows for any `a`, with `3 b R mod p` at `B3P`. -/
def exchangeBrainpoolP256r1 : Prog isa :=
  Cfg.exchangeWith Impl.Ecdsa.PPC64LE.brainpoolp256r1 (Impl.Ecdsa.PPC64LE.WindowA.Cfg.mul Impl.Ecdsa.PPC64LE.brainpoolp256r1 PX PY Impl.Ecdsa.PPC64LE.B3P)

end VG.Impl.Ecdh.PPC64LE
