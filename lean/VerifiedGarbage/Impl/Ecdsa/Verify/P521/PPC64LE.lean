module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3

/-! # `vg_ecdsa_p521_verify` on PPC64LE

`[u]G` by the signed seven-bit comb of P-521's public keys, with the addition
inlined (`Impl/Ecdsa/P521/PPC64LEComb.lean`), `[v]Q` by ECDH's three-bit
windows (`Impl/Ecdsa/PPC64LE/Window3.lean`, with `b` in Montgomery's form at
`EM`), and their sum (`Cfg.pointsWith`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `[u]G + [v]Q` for P-521. -/
def pointsP521 : Prog isa :=
  Cfg.pointsWith Impl.Ecdsa.PPC64LE.p521 Impl.Weierstrass.PPC64LE.mulGeneratorP521
    (Impl.Ecdsa.PPC64LE.Window.Cfg.mul3 Impl.Ecdsa.PPC64LE.p521 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY
      Impl.Ecdsa.PPC64LE.EM)

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa := Cfg.verifyWith Impl.Ecdsa.PPC64LE.p521 pointsP521

end VG.Impl.Ecdsa.Verify.PPC64LE
