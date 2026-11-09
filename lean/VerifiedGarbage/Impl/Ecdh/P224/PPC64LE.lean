module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window

/-! # ECDH over P-224 on PPC64LE: four-word field elements and scalars, `[d]P` by windows -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_p224`: `[d]P` by four-bit windows, with `b R mod p` at `BP`. -/
def exchangeP224 : Prog isa :=
  Cfg.exchangeWith Impl.Ecdsa.PPC64LE.p224 (Impl.Ecdsa.PPC64LE.Window.Cfg.mul Impl.Ecdsa.PPC64LE.p224 PX PY BP)

end VG.Impl.Ecdh.PPC64LE
