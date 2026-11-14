module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window

/-! # `vg_ecdsa_p384_verify` on PPC64LE

`[u]G` by the signed seven-bit comb of P-384's public keys
(`Impl/Ecdsa/P384/PPC64LEComb.lean`), `[v]Q` by ECDH's four-bit windows
(`Impl/Ecdsa/PPC64LE/Window.lean`, with `b` in Montgomery's form at `EM`),
and their sum (`Cfg.pointsWith`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `[u]G + [v]Q` for P-384. -/
def pointsP384 : Prog isa :=
  Cfg.pointsWith Impl.Ecdsa.PPC64LE.p384 Impl.Weierstrass.PPC64LE.mulGeneratorP384
    (Impl.Ecdsa.PPC64LE.Window.Cfg.mul Impl.Ecdsa.PPC64LE.p384 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY
      Impl.Ecdsa.PPC64LE.EM)

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa := Cfg.verifyWith Impl.Ecdsa.PPC64LE.p384 pointsP384

end VG.Impl.Ecdsa.Verify.PPC64LE
