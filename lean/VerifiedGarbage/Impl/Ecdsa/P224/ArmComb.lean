module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Impl.Ecdsa.P224.Arm
public import VerifiedGarbage.Impl.P224.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! # P-224's generator by the shared signed seven-bit comb on 32-bit ARM

The comb of `TComb.lean` with the first 32 of P-224's tables (`Impl/P224/CombTable7.lean`, the
x86-64 comb's, which has 37), and signing, public-key derivation and verification with it
in place of the ladder for `[k]G`. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

def p224Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.p224
  let start := VG.Impl.P224.p224Comb7Start32
  { L := c.ladderCfg, F := c.SP, w := 7, J := 32, tsym := "VG_P224_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x }

@[irreducible] def p224CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 4 (2^256) VG.Spec.P224.curve.p VG.Impl.P224.p224Comb7x32

def p224CombConsts : List (String × List (BitVec 64)) :=
  [(p224Comb.tsym,p224CombWords)]

def mulGeneratorP224 : Prog VG.Arm.isa := p224Comb.comb

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

def signP224Comb : Prog VG.Arm.isa := p224.signWith Weierstrass.Arm.mulGeneratorP224

def publicKeyP224Comb : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith p224 Weierstrass.Arm.mulGeneratorP224

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_p224_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorP224 : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (p224.sl K) (bitsAt p224.n 0) (8 * p224.n)) Weierstrass.Arm.mulGeneratorP224

def verifyP224Comb : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith p224 verifyGeneratorP224

end VG.Impl.Ecdsa.Arm
