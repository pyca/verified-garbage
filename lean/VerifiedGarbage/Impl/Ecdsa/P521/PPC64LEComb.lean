module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
public import VerifiedGarbage.Impl.P521.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.PPC64LE

/-! # P-521's generator by the signed seven-bit comb on PPC64LE

The comb of `Impl/Weierstrass/PPC64LE/TComb.lean` with P-521's tables
(`Impl/P521/CombTable7.lean`, the other targets'), and public keys with it in
place of the ladder for `[d]G`, and signatures with it for `[k]G`. -/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

/-- P-521's comb, on the signature's layout: its ladder's `R`, `a`, `3b` and
table of the scalar's bits, zero at `ZERO` and `-y` in the ladder's `T`. -/
def p521Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.PPC64LE.p521
  let start := VG.Impl.P521.p521Comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 83, tsym := "VG_P521_COMB"
    start := (c.mont start.1, c.mont start.2)
    one := c.R % c.C.p, zero := c.sl VG.Impl.Ecdsa.PPC64LE.ZERO, neg := c.ladderCfg.T.x }

/-- The table's words, in Montgomery's form. -/
@[irreducible] def p521CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 9 (2 ^ 576) VG.Spec.P521.curve.p VG.Impl.P521.p521Comb7

def p521CombConsts : List (String × List (BitVec 64)) := [(p521Comb.tsym, p521CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorP521 : Prog VG.PPC64LE.isa := p521Comb.comb

end VG.Impl.Weierstrass.PPC64LE

namespace VG.Impl.EcKey.PPC64LE

/-- `vg_ec_p521_public_key`, with `[d]G` by the comb. -/
def publicKeyP521Comb : Prog VG.PPC64LE.isa :=
  Cfg.publicKeyWith Impl.Ecdsa.PPC64LE.p521 Weierstrass.PPC64LE.mulGeneratorP521

end VG.Impl.EcKey.PPC64LE

namespace VG.Impl.Ecdsa.PPC64LE

/-- `vg_ecdsa_p521_sign`, with `[k]G` by the comb. -/
def signP521Comb : Prog VG.PPC64LE.isa := p521.signWith Weierstrass.PPC64LE.mulGeneratorP521

end VG.Impl.Ecdsa.PPC64LE
