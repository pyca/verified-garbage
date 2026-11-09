module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3

/-! # ECDH over P-521 on PPC64LE: nine-word field elements and scalars, `[d]P` by three-bit windows -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_p521`: `[d]P` by three-bit windows, with `b R mod p` at `BP`. -/
def exchangeP521 : Prog isa :=
  Cfg.exchangeWith Impl.Ecdsa.PPC64LE.p521 (Impl.Ecdsa.PPC64LE.Window.Cfg.mul3 Impl.Ecdsa.PPC64LE.p521 PX PY BP)

end VG.Impl.Ecdh.PPC64LE
