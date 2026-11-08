module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Impl.BrainpoolP256r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.PPC64LE

/-! # brainpoolP256r1's generator by the signed seven-bit comb on PPC64LE

The comb of `Impl/Weierstrass/PPC64LE/TComb.lean` with brainpoolP256r1's tables
(`Impl/BrainpoolP256r1/CombTable7.lean`, the other targets'), and public keys with it in
place of the ladder for `[d]G`, and signatures with it for `[k]G`. -/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE

/-- brainpoolP256r1's comb, on the signature's layout: its ladder's `R`, `a`, `3b` and
table of the scalar's bits, zero at `ZERO` and `-y` in the ladder's `T`. -/
def brainpoolp256r1Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.PPC64LE.brainpoolp256r1
  let start := VG.Impl.BrainpoolP256r1.comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 37, tsym := "VG_BRAINPOOLP256R1_COMB"
    start := (c.mont start.1, c.mont start.2)
    one := c.R % c.C.p, zero := c.sl VG.Impl.Ecdsa.PPC64LE.ZERO, neg := c.ladderCfg.T.x }

/-- The table's words, in Montgomery's form. -/
@[irreducible] def brainpoolp256r1CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 4 (2 ^ 256) VG.Spec.BrainpoolP256r1.curve.p VG.Impl.BrainpoolP256r1.comb7

def brainpoolp256r1CombConsts : List (String × List (BitVec 64)) := [(brainpoolp256r1Comb.tsym, brainpoolp256r1CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorBrainpoolP256r1 : Prog VG.PPC64LE.isa := brainpoolp256r1Comb.comb

end VG.Impl.Weierstrass.PPC64LE

namespace VG.Impl.EcKey.PPC64LE

/-- `vg_ec_brainpoolp256r1_public_key`, with `[d]G` by the comb. -/
def publicKeyBrainpoolP256r1Comb : Prog VG.PPC64LE.isa :=
  Cfg.publicKeyWith Impl.Ecdsa.PPC64LE.brainpoolp256r1 Weierstrass.PPC64LE.mulGeneratorBrainpoolP256r1

end VG.Impl.EcKey.PPC64LE

namespace VG.Impl.Ecdsa.PPC64LE

/-- `vg_ecdsa_brainpoolp256r1_sign`, with `[k]G` by the comb. -/
def signBrainpoolP256r1Comb : Prog VG.PPC64LE.isa := brainpoolp256r1.signWith Weierstrass.PPC64LE.mulGeneratorBrainpoolP256r1

end VG.Impl.Ecdsa.PPC64LE
