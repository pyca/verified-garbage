module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window

/-! # `vg_ecdsa_p256_verify` on PPC64LE

`[u]G` by the signed seven-bit comb of P-256's public keys
(`Impl/Ecdsa/P256/PPC64LEComb.lean`), `[v]Q` by ECDH's four-bit windows
(`Impl/Ecdsa/PPC64LE/Window.lean`, with `b` in Montgomery's form at `EM`),
and their sum (`Cfg.pointsWith`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `[u]G + [v]Q` for P-256. -/
def pointsP256 : Prog isa :=
  Cfg.pointsWith Impl.Ecdsa.PPC64LE.p256 Impl.Weierstrass.PPC64LE.mulGeneratorP256
    (Impl.Ecdsa.PPC64LE.Window.Cfg.mul Impl.Ecdsa.PPC64LE.p256 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY
      Impl.Ecdsa.PPC64LE.EM)

/-- `vg_ecdsa_p256_verify`. -/
def verifyP256 : Prog isa := Cfg.verifyWith Impl.Ecdsa.PPC64LE.p256 pointsP256

end VG.Impl.Ecdsa.Verify.PPC64LE
