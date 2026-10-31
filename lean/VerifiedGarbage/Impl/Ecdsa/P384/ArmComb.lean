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

/-- The comb, its point additions by `vg_p384_point_add_umaal` if `u`. -/
def p384CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.p384With u
  let start := VG.Impl.P384.p384Comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 55, tsym := "VG_P384_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x, u := u }

def p384Comb : TCombCfg := p384CombWith false

@[irreducible] def p384CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 6 (2^384) VG.Spec.P384.curve.p VG.Impl.P384.p384Comb7

def p384CombConsts : List (String × List (BitVec 64)) :=
  [(p384Comb.tsym,p384CombWords)]

def mulGeneratorP384With (u : Bool) : Prog VG.Arm.isa := (p384CombWith u).comb

def mulGeneratorP384 : Prog VG.Arm.isa := mulGeneratorP384With false

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

def signP384CombWith (u : Bool) : Prog VG.Arm.isa :=
  (p384With u).signWith (Weierstrass.Arm.mulGeneratorP384With u)

def signP384Comb : Prog VG.Arm.isa := signP384CombWith false

def signP384CombU : Prog VG.Arm.isa := signP384CombWith true

def publicKeyP384CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (p384With u) (Weierstrass.Arm.mulGeneratorP384With u)

def publicKeyP384Comb : Prog VG.Arm.isa := publicKeyP384CombWith false

def publicKeyP384CombU : Prog VG.Arm.isa := publicKeyP384CombWith true

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_p384_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorP384With (u : Bool) : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (p384.sl K) (bitsAt p384.n 0) (8 * p384.n)) (Weierstrass.Arm.mulGeneratorP384With u)

def verifyGeneratorP384 : Prog VG.Arm.isa := verifyGeneratorP384With false

def verifyP384CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (p384With u) (verifyGeneratorP384With u)

def verifyP384Comb : Prog VG.Arm.isa := verifyP384CombWith false

def verifyP384CombU : Prog VG.Arm.isa := verifyP384CombWith true

end VG.Impl.Ecdsa.Arm
