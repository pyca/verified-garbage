module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Impl.BrainpoolP384r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.PPC64LE

/-! # brainpoolBrainpoolP384r1r1's generator by the signed seven-bit comb on PPC64LE

The comb of `Impl/Weierstrass/PPC64LE/TComb.lean` with brainpoolBrainpoolP384r1r1's tables
(`Impl/BrainpoolP384r1/CombTable7.lean`, the other targets'), and public keys with it in
place of the ladder for `[d]G`, and signatures with it for `[k]G`. -/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

/-- brainpoolBrainpoolP384r1r1's comb, on the signature's layout: its ladder's `R`, `a`, `3b` and
table of the scalar's bits, zero at `ZERO` and `-y` in the ladder's `T`. -/
def brainpoolp384r1Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.PPC64LE.brainpoolp384r1
  let start := VG.Impl.BrainpoolP384r1.comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 55, tsym := "VG_BRAINPOOLP384R1_COMB"
    start := (c.mont start.1, c.mont start.2)
    one := c.R % c.C.p, zero := c.sl VG.Impl.Ecdsa.PPC64LE.ZERO, neg := c.ladderCfg.T.x }

/-- The table's words, in Montgomery's form. -/
@[irreducible] def brainpoolp384r1CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 6 (2 ^ 384) VG.Spec.BrainpoolP384r1.curve.p VG.Impl.BrainpoolP384r1.comb7

def brainpoolp384r1CombConsts : List (String × List (BitVec 64)) := [(brainpoolp384r1Comb.tsym, brainpoolp384r1CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorBrainpoolP384r1 : Prog VG.PPC64LE.isa := brainpoolp384r1Comb.comb

end VG.Impl.Weierstrass.PPC64LE

namespace VG.Impl.EcKey.PPC64LE

/-- `vg_ec_brainpoolp384r1_public_key`, with `[d]G` by the comb. -/
def publicKeyBrainpoolP384r1Comb : Prog VG.PPC64LE.isa :=
  Cfg.publicKeyWith Impl.Ecdsa.PPC64LE.brainpoolp384r1 Weierstrass.PPC64LE.mulGeneratorBrainpoolP384r1

end VG.Impl.EcKey.PPC64LE

namespace VG.Impl.Ecdsa.PPC64LE

/-- `vg_ecdsa_brainpoolp384r1_sign`, with `[k]G` by the comb. -/
def signBrainpoolP384r1Comb : Prog VG.PPC64LE.isa := brainpoolp384r1.signWith Weierstrass.PPC64LE.mulGeneratorBrainpoolP384r1

end VG.Impl.Ecdsa.PPC64LE
