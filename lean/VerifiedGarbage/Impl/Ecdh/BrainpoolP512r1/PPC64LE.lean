module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3A

/-! # ECDH over brainpoolP512r1 on PPC64LE: eight-word field elements and scalars, `[d]P` by three-bit windows -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_brainpoolp512r1`: `[d]P` by three-bit windows for any `a`, from the
scalar's top two bits, with `3 b R mod p` at `B3P`. -/
def exchangeBrainpoolP512r1 : Prog isa :=
  Cfg.exchangeWith Impl.Ecdsa.PPC64LE.brainpoolp512r1
    (Impl.Ecdsa.PPC64LE.WindowA.Cfg.mul3top Impl.Ecdsa.PPC64LE.brainpoolp512r1 PX PY Impl.Ecdsa.PPC64LE.B3P)

end VG.Impl.Ecdh.PPC64LE
