module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TCombI
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Impl.BrainpoolP512r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.PPC64LE

/-! # brainpoolP512r1's generator by the signed seven-bit comb on PPC64LE

The comb with the addition inlined (`Impl/Weierstrass/PPC64LE/TCombI.lean`;
brainpoolP512r1's eight-word coordinates do not fit the point functions') with brainpoolP512r1's
tables (`Impl/BrainpoolP512r1/CombTable7.lean`, the other targets'): 74 windows of
seven bits over the ladder's table of the scalar's bits, all `64 n = 512` of
them. Public keys and signatures with it in place of the ladder. -/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

/-- brainpoolP512r1's comb, on the signature's layout: the ladder's `R`, `a`, `3b` and
table of bits (of 512 bits), the entry in the ladder's `T`, the sum in its
`D`, `-y` in `D`'s `x` before it, and zero at `ZERO`. -/
def brainpoolp512r1Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.PPC64LE.brainpoolp512r1
  let start := VG.Impl.BrainpoolP512r1.comb7Start
  { L := { c.ladderCfg with nbits := 64 * c.n }, F := c.SP, w := 7, J := 74, tsym := "VG_BRAINPOOLP512R1_COMB"
    start := (c.mont start.1, c.mont start.2)
    one := c.R % c.C.p, zero := c.sl VG.Impl.Ecdsa.PPC64LE.ZERO, neg := c.sl VG.Impl.Ecdsa.PPC64LE.DX
    qBase := c.sl VG.Impl.Ecdsa.PPC64LE.TX }

/-- The table's words, in Montgomery's form. -/
@[irreducible] def brainpoolp512r1CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 8 (2 ^ 512) VG.Spec.BrainpoolP512r1.curve.p VG.Impl.BrainpoolP512r1.comb7

def brainpoolp512r1CombConsts : List (String × List (BitVec 64)) := [(brainpoolp512r1Comb.tsym, brainpoolp512r1CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorBrainpoolP512r1 : Prog VG.PPC64LE.isa := brainpoolp512r1Comb.combI

end VG.Impl.Weierstrass.PPC64LE

namespace VG.Impl.EcKey.PPC64LE

/-- `vg_ec_brainpoolp512r1_public_key`, with `[d]G` by the comb. -/
def publicKeyBrainpoolP512r1Comb : Prog VG.PPC64LE.isa :=
  Cfg.publicKeyWith Impl.Ecdsa.PPC64LE.brainpoolp512r1 Weierstrass.PPC64LE.mulGeneratorBrainpoolP512r1

end VG.Impl.EcKey.PPC64LE

namespace VG.Impl.Ecdsa.PPC64LE

/-- `vg_ecdsa_brainpoolp512r1_sign`, with `[k]G` by the comb. -/
def signBrainpoolP512r1Comb : Prog VG.PPC64LE.isa := brainpoolp512r1.signWith Weierstrass.PPC64LE.mulGeneratorBrainpoolP512r1

end VG.Impl.Ecdsa.PPC64LE
