module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE
public import VerifiedGarbage.Impl.P256.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.PPC64LE

/-! # P-256's generator by the signed seven-bit comb on PPC64LE

The comb of `Impl/Weierstrass/PPC64LE/TComb.lean` with P-256's tables
(`Impl/P256/CombTable7.lean`, the other targets'), and public keys with it in
place of the ladder for `[d]G`, and signatures with it for `[k]G`. -/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

/-- P-256's comb, on the signature's layout: its ladder's `R`, `a`, `3b` and
table of the scalar's bits, zero at `ZERO` and `-y` in the ladder's `T`. -/
def p256Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.PPC64LE.p256
  let start := VG.Impl.P256.p256Comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 37, tsym := "VG_P256_COMB"
    start := (c.mont start.1, c.mont start.2)
    one := c.R % c.C.p, zero := c.sl VG.Impl.Ecdsa.PPC64LE.ZERO, neg := c.ladderCfg.T.x }

/-- The table's words, in Montgomery's form. -/
@[irreducible] def p256CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 4 (2 ^ 256) VG.Spec.P256.curve.p VG.Impl.P256.p256Comb7

def p256CombConsts : List (String × List (BitVec 64)) := [(p256Comb.tsym, p256CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorP256 : Prog VG.PPC64LE.isa := p256Comb.comb

end VG.Impl.Weierstrass.PPC64LE

namespace VG.Impl.EcKey.PPC64LE

/-- `vg_ec_p256_public_key`, with `[d]G` by the comb. -/
def publicKeyP256Comb : Prog VG.PPC64LE.isa :=
  Cfg.publicKeyWith Impl.Ecdsa.PPC64LE.p256 Weierstrass.PPC64LE.mulGeneratorP256

end VG.Impl.EcKey.PPC64LE

namespace VG.Impl.Ecdsa.PPC64LE

/-- `vg_ecdsa_p256_sign`, with `[k]G` by the comb. -/
def signP256Comb : Prog VG.PPC64LE.isa := p256.signWith Weierstrass.PPC64LE.mulGeneratorP256

end VG.Impl.Ecdsa.PPC64LE
