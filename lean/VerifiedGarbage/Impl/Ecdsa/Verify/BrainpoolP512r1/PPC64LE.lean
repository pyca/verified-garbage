module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3A

/-! # `vg_ecdsa_brainpoolp512r1_verify` on PPC64LE

`[u]G` by the signed seven-bit comb of brainpoolP512r1's public keys, with the
addition inlined (`Impl/Ecdsa/BrainpoolP512r1/PPC64LEComb.lean`), `[v]Q` by
ECDH's three-bit windows for any `a` (`Impl/Ecdsa/PPC64LE/Window3A.lean`, with
`3 b` at `B3P`), and their sum (`Cfg.pointsWith`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `[u]G + [v]Q` for brainpoolP512r1. -/
def pointsBrainpoolP512r1 : Prog isa :=
  Cfg.pointsWith Impl.Ecdsa.PPC64LE.brainpoolp512r1 Impl.Weierstrass.PPC64LE.mulGeneratorBrainpoolP512r1
    (Impl.Ecdsa.PPC64LE.WindowA.Cfg.mul3top Impl.Ecdsa.PPC64LE.brainpoolp512r1 Impl.Ecdh.PPC64LE.PX
      Impl.Ecdh.PPC64LE.PY Impl.Ecdsa.PPC64LE.B3P)

/-- `vg_ecdsa_brainpoolp512r1_verify`. -/
def verifyBrainpoolP512r1 : Prog isa := Cfg.verifyWith Impl.Ecdsa.PPC64LE.brainpoolp512r1 pointsBrainpoolP512r1

end VG.Impl.Ecdsa.Verify.PPC64LE
