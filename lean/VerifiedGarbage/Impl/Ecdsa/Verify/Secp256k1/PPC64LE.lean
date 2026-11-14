module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.WindowA

/-! # `vg_ecdsa_secp256k1_verify` on PPC64LE

`[u]G` by the signed seven-bit comb of secp256k1's public keys
(`Impl/Ecdsa/Secp256k1/PPC64LEComb.lean`), `[v]Q` by the four-bit windows for
any `a` (`Impl/Ecdsa/PPC64LE/WindowA.lean`, with `3 b` at `B3P`; brainpoolP256r1's
ECDH uses them, secp256k1's the ladder), and their sum (`Cfg.pointsWith`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `[u]G + [v]Q` for secp256k1. -/
def pointsSecp256k1 : Prog isa :=
  Cfg.pointsWith Impl.Ecdsa.PPC64LE.secp256k1 Impl.Weierstrass.PPC64LE.mulGeneratorSecp256k1
    (Impl.Ecdsa.PPC64LE.WindowA.Cfg.mul Impl.Ecdsa.PPC64LE.secp256k1 Impl.Ecdh.PPC64LE.PX
      Impl.Ecdh.PPC64LE.PY Impl.Ecdsa.PPC64LE.B3P)

/-- `vg_ecdsa_secp256k1_verify`. -/
def verifySecp256k1 : Prog isa := Cfg.verifyWith Impl.Ecdsa.PPC64LE.secp256k1 pointsSecp256k1

end VG.Impl.Ecdsa.Verify.PPC64LE
