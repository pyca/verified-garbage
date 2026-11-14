module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window

/-! # `vg_ecdsa_p224_verify` on PPC64LE

`[u]G` by the signed seven-bit comb of P-224's public keys
(`Impl/Ecdsa/P224/PPC64LEComb.lean`), `[v]Q` by ECDH's four-bit windows
(`Impl/Ecdsa/PPC64LE/Window.lean`, with `b` in Montgomery's form at `EM`),
and their sum (`Cfg.pointsWith`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `[u]G + [v]Q` for P-224. -/
def pointsP224 : Prog isa :=
  Cfg.pointsWith Impl.Ecdsa.PPC64LE.p224 Impl.Weierstrass.PPC64LE.mulGeneratorP224
    (Impl.Ecdsa.PPC64LE.Window.Cfg.mul Impl.Ecdsa.PPC64LE.p224 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY
      Impl.Ecdsa.PPC64LE.EM)

/-- `vg_ecdsa_p224_verify`. -/
def verifyP224 : Prog isa := Cfg.verifyWith Impl.Ecdsa.PPC64LE.p224 pointsP224

end VG.Impl.Ecdsa.Verify.PPC64LE
