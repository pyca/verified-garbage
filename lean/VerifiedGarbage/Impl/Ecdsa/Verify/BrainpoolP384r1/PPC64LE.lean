module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.WindowA

/-! # `vg_ecdsa_brainpoolp384r1_verify` on PPC64LE

`[u]G` by the signed seven-bit comb of brainpoolP384r1's public keys
(`Impl/Ecdsa/BrainpoolP384r1/PPC64LEComb.lean`), `[v]Q` by ECDH's four-bit windows
for any `a` (`Impl/Ecdsa/PPC64LE/WindowA.lean`, with `3 b` at `B3P`), and their sum
(`Cfg.pointsWith`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `[u]G + [v]Q` for brainpoolP384r1. -/
def pointsBrainpoolP384r1 : Prog isa :=
  Cfg.pointsWith Impl.Ecdsa.PPC64LE.brainpoolp384r1 Impl.Weierstrass.PPC64LE.mulGeneratorBrainpoolP384r1
    (Impl.Ecdsa.PPC64LE.WindowA.Cfg.mul Impl.Ecdsa.PPC64LE.brainpoolp384r1 Impl.Ecdh.PPC64LE.PX
      Impl.Ecdh.PPC64LE.PY Impl.Ecdsa.PPC64LE.B3P)

/-- `vg_ecdsa_brainpoolp384r1_verify`. -/
def verifyBrainpoolP384r1 : Prog isa := Cfg.verifyWith Impl.Ecdsa.PPC64LE.brainpoolp384r1 pointsBrainpoolP384r1

end VG.Impl.Ecdsa.Verify.PPC64LE
