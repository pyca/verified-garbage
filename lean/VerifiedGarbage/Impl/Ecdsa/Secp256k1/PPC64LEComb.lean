module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
public import VerifiedGarbage.Impl.Secp256k1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.PPC64LE

/-! # secp256k1's generator by the signed seven-bit comb on PPC64LE

The comb of `Impl/Weierstrass/PPC64LE/TComb.lean` with secp256k1's tables
(`Impl/Secp256k1/CombTable7.lean`, the other targets'), and public keys with it in
place of the ladder for `[d]G`, and signatures with it for `[k]G`. -/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

/-- secp256k1's comb, on the signature's layout: its ladder's `R`, `a`, `3b` and
table of the scalar's bits, zero at `ZERO` and `-y` in the ladder's `T`. -/
def secp256k1Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.PPC64LE.secp256k1
  let start := VG.Impl.Secp256k1.secp256k1Comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 37, tsym := "VG_SECP256K1_COMB"
    start := (c.mont start.1, c.mont start.2)
    one := c.R % c.C.p, zero := c.sl VG.Impl.Ecdsa.PPC64LE.ZERO, neg := c.ladderCfg.T.x }

/-- The table's words, in Montgomery's form. -/
@[irreducible] def secp256k1CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 4 (2 ^ 256) VG.Spec.Secp256k1.curve.p VG.Impl.Secp256k1.secp256k1Comb7

def secp256k1CombConsts : List (String × List (BitVec 64)) := [(secp256k1Comb.tsym, secp256k1CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorSecp256k1 : Prog VG.PPC64LE.isa := secp256k1Comb.comb

end VG.Impl.Weierstrass.PPC64LE

namespace VG.Impl.EcKey.PPC64LE

/-- `vg_ec_secp256k1_public_key`, with `[d]G` by the comb. -/
def publicKeySecp256k1Comb : Prog VG.PPC64LE.isa :=
  Cfg.publicKeyWith Impl.Ecdsa.PPC64LE.secp256k1 Weierstrass.PPC64LE.mulGeneratorSecp256k1

end VG.Impl.EcKey.PPC64LE

namespace VG.Impl.Ecdsa.PPC64LE

/-- `vg_ecdsa_secp256k1_sign`, with `[k]G` by the comb. -/
def signSecp256k1Comb : Prog VG.PPC64LE.isa := secp256k1.signWith Weierstrass.PPC64LE.mulGeneratorSecp256k1

end VG.Impl.Ecdsa.PPC64LE
