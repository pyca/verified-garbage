module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
public import VerifiedGarbage.Impl.P224.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.PPC64LE

/-! # P-224's generator by the signed seven-bit comb on PPC64LE

The comb of `Impl/Weierstrass/PPC64LE/TComb.lean` with P-224's tables
(`Impl/P224/CombTable7.lean`, the other targets'), and public keys with it in
place of the ladder for `[d]G`, and signatures with it for `[k]G`. -/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

/-- P-224's comb, on the signature's layout: its ladder's `R`, `a`, `3b` and
table of the scalar's bits, zero at `ZERO` and `-y` in the ladder's `T`. -/
def p224Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.PPC64LE.p224
  let start := VG.Impl.P224.p224Comb7Start32
  { L := c.ladderCfg, F := c.SP, w := 7, J := 32, tsym := "VG_P224_COMB"
    start := (c.mont start.1, c.mont start.2)
    one := c.R % c.C.p, zero := c.sl VG.Impl.Ecdsa.PPC64LE.ZERO, neg := c.ladderCfg.T.x }

/-- The table's words, in Montgomery's form. -/
@[irreducible] def p224CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 4 (2 ^ 256) VG.Spec.P224.curve.p VG.Impl.P224.p224Comb7x32

def p224CombConsts : List (String × List (BitVec 64)) := [(p224Comb.tsym, p224CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorP224 : Prog VG.PPC64LE.isa := p224Comb.comb

end VG.Impl.Weierstrass.PPC64LE

namespace VG.Impl.EcKey.PPC64LE

/-- `vg_ec_p224_public_key`, with `[d]G` by the comb. -/
def publicKeyP224Comb : Prog VG.PPC64LE.isa :=
  Cfg.publicKeyWith Impl.Ecdsa.PPC64LE.p224 Weierstrass.PPC64LE.mulGeneratorP224

end VG.Impl.EcKey.PPC64LE

namespace VG.Impl.Ecdsa.PPC64LE

/-- `vg_ecdsa_p224_sign`, with `[k]G` by the comb. -/
def signP224Comb : Prog VG.PPC64LE.isa := p224.signWith Weierstrass.PPC64LE.mulGeneratorP224

end VG.Impl.Ecdsa.PPC64LE
