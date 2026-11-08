module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE
public import VerifiedGarbage.Impl.P384.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.PPC64LE

/-! # P-384's generator by the signed seven-bit comb on PPC64LE

The comb of `Impl/Weierstrass/PPC64LE/TComb.lean` with P-384's tables
(`Impl/P384/CombTable7.lean`, the other targets'), and public keys with it in
place of the ladder for `[d]G`, and signatures with it for `[k]G`. -/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

/-- P-384's comb, on the signature's layout: its ladder's `R`, `a`, `3b` and
table of the scalar's bits, zero at `ZERO` and `-y` in the ladder's `T`. -/
def p384Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.PPC64LE.p384
  let start := VG.Impl.P384.p384Comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 55, tsym := "VG_P384_COMB"
    start := (c.mont start.1, c.mont start.2)
    one := c.R % c.C.p, zero := c.sl VG.Impl.Ecdsa.PPC64LE.ZERO, neg := c.ladderCfg.T.x }

/-- The table's words, in Montgomery's form. -/
@[irreducible] def p384CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 6 (2 ^ 384) VG.Spec.P384.curve.p VG.Impl.P384.p384Comb7

def p384CombConsts : List (String × List (BitVec 64)) := [(p384Comb.tsym, p384CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorP384 : Prog VG.PPC64LE.isa := p384Comb.comb

end VG.Impl.Weierstrass.PPC64LE

namespace VG.Impl.EcKey.PPC64LE

/-- `vg_ec_p384_public_key`, with `[d]G` by the comb. -/
def publicKeyP384Comb : Prog VG.PPC64LE.isa :=
  Cfg.publicKeyWith Impl.Ecdsa.PPC64LE.p384 Weierstrass.PPC64LE.mulGeneratorP384

end VG.Impl.EcKey.PPC64LE

namespace VG.Impl.Ecdsa.PPC64LE

/-- `vg_ecdsa_p384_sign`, with `[k]G` by the comb. -/
def signP384Comb : Prog VG.PPC64LE.isa := p384.signWith Weierstrass.PPC64LE.mulGeneratorP384

end VG.Impl.Ecdsa.PPC64LE
