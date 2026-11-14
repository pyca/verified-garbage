module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TCombI
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
public import VerifiedGarbage.Impl.P521.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.PPC64LE

/-! # P-521's generator by the signed seven-bit comb on PPC64LE

The comb with the addition inlined (`Impl/Weierstrass/PPC64LE/TCombI.lean`;
P-521's nine-word coordinates do not fit the point functions') with P-521's
tables (`Impl/P521/CombTable7.lean`, the other targets'): 83 windows of
seven bits over the ladder's table of the scalar's bits, all `64 n = 576` of
them. Public keys and signatures with it in place of the ladder. -/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

/-- P-521's comb, on the signature's layout: the ladder's `R`, `a`, `3b` and
table of bits (of 576 bits), the entry in the ladder's `T`, the sum in its
`D`, `-y` in `D`'s `x` before it, and zero at `ZERO`. -/
def p521Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.PPC64LE.p521
  let start := VG.Impl.P521.p521Comb7Start
  { L := { c.ladderCfg with nbits := 64 * c.n }, F := c.SP, w := 7, J := 83, tsym := "VG_P521_COMB"
    start := (c.mont start.1, c.mont start.2)
    one := c.R % c.C.p, zero := c.sl VG.Impl.Ecdsa.PPC64LE.ZERO, neg := c.sl VG.Impl.Ecdsa.PPC64LE.DX
    qBase := c.sl VG.Impl.Ecdsa.PPC64LE.TX }

/-- The table's words, in Montgomery's form. -/
@[irreducible] def p521CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 9 (2 ^ 576) VG.Spec.P521.curve.p VG.Impl.P521.p521Comb7

def p521CombConsts : List (String × List (BitVec 64)) := [(p521Comb.tsym, p521CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorP521 : Prog VG.PPC64LE.isa := p521Comb.combI

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
