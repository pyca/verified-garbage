module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Impl.Ecdsa.P384.Arm
public import VerifiedGarbage.Impl.P384.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! # P-384's generator by the shared signed seven-bit comb on 32-bit ARM

The comb of `TComb.lean` with P-384's tables (`Impl/P384/CombTable7.lean`, the
x86-64 comb's), and signing, public-key derivation and verification with it
in place of the ladder for `[k]G`. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

def p384Comb : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.p384
  let start := VG.Impl.P384.p384Comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 55, tsym := "VG_P384_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x }

@[irreducible] def p384CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 6 (2^384) VG.Spec.P384.curve.p VG.Impl.P384.p384Comb7

def p384CombConsts : List (String × List (BitVec 64)) :=
  [(p384Comb.tsym,p384CombWords)]

def mulGeneratorP384 : Prog VG.Arm.isa := p384Comb.comb

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

def signP384Comb : Prog VG.Arm.isa := p384.signWith Weierstrass.Arm.mulGeneratorP384

def publicKeyP384Comb : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith p384 Weierstrass.Arm.mulGeneratorP384

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_p384_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorP384 : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (p384.sl K) (bitsAt p384.n 0) (8 * p384.n)) Weierstrass.Arm.mulGeneratorP384

def verifyP384Comb : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith p384 verifyGeneratorP384

end VG.Impl.Ecdsa.Arm
