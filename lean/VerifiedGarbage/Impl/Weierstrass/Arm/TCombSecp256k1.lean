module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm
public import VerifiedGarbage.Impl.Secp256k1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-! The secp256k1 generator uses the existing signed seven-bit comb format. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

/-- The comb, its point additions by `vg_secp256k1_point_add_umaal` if `u`. -/
def secp256k1CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.secp256k1With u
  let start := VG.Impl.Secp256k1.secp256k1Comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 37, tsym := "VG_SECP256K1_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x, u := u }

def secp256k1Comb : TCombCfg := secp256k1CombWith false

@[irreducible] def secp256k1CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 4 (2^256) VG.Spec.Secp256k1.curve.p
    VG.Impl.Secp256k1.secp256k1Comb7

def secp256k1CombConsts : List (String × List (BitVec 64)) :=
  [(secp256k1Comb.tsym,secp256k1CombWords)]

def mulGeneratorSecp256k1With (u : Bool) : Prog VG.Arm.isa := (secp256k1CombWith u).comb

def mulGeneratorSecp256k1 : Prog VG.Arm.isa := mulGeneratorSecp256k1With false

end VG.Impl.Weierstrass.Arm
