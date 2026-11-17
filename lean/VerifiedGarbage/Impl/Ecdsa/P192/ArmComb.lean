module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Impl.Ecdsa.P192.Arm
public import VerifiedGarbage.Impl.P192.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! # P-192's generator by the shared signed seven-bit comb on 32-bit ARM

The comb of `TComb.lean` with P-192's tables (`Impl/P192/CombTable7.lean`), and signing, public-key derivation and verification with it
in place of the ladder for `[k]G`. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

/-- The comb, its point additions by `vg_p192_point_add_umaal` if `u`. -/
def p192CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.p192With u
  let start := VG.Impl.P192.comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 28, tsym := "VG_P192_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x, u := u }

def p192Comb : TCombCfg := p192CombWith false

@[irreducible] def p192CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 3 (2^192) VG.Spec.P192.curve.p VG.Impl.P192.comb7

def p192CombConsts : List (String × List (BitVec 64)) :=
  [(p192Comb.tsym,p192CombWords)]

def mulGeneratorP192With (u : Bool) : Prog VG.Arm.isa := (p192CombWith u).comb

def mulGeneratorP192 : Prog VG.Arm.isa := mulGeneratorP192With false

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

def signP192CombWith (u : Bool) : Prog VG.Arm.isa :=
  (p192With u).signWith (Weierstrass.Arm.mulGeneratorP192With u)

def signP192Comb : Prog VG.Arm.isa := signP192CombWith false

def signP192CombU : Prog VG.Arm.isa := signP192CombWith true

def publicKeyP192CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (p192With u) (Weierstrass.Arm.mulGeneratorP192With u)

def publicKeyP192Comb : Prog VG.Arm.isa := publicKeyP192CombWith false

def publicKeyP192CombU : Prog VG.Arm.isa := publicKeyP192CombWith true

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_p192_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorP192With (u : Bool) : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (p192.sl K) (bitsAt p192.n 0) (8 * p192.n)) (Weierstrass.Arm.mulGeneratorP192With u)

def verifyP192CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (p192With u) (verifyGeneratorP192With u)

def verifyP192Comb : Prog VG.Arm.isa := verifyP192CombWith false

def verifyP192CombU : Prog VG.Arm.isa := verifyP192CombWith true

end VG.Impl.Ecdsa.Arm
