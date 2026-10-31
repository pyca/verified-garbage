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

/-- The comb, its point additions by `vg_p224_point_add_umaal` if `u`. -/
def p224CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.p224With u
  let start := VG.Impl.P224.p224Comb7Start32
  { L := c.ladderCfg, F := c.SP, w := 7, J := 32, tsym := "VG_P224_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x, u := u }

def p224Comb : TCombCfg := p224CombWith false

@[irreducible] def p224CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 4 (2^256) VG.Spec.P224.curve.p VG.Impl.P224.p224Comb7x32

def p224CombConsts : List (String × List (BitVec 64)) :=
  [(p224Comb.tsym,p224CombWords)]

def mulGeneratorP224With (u : Bool) : Prog VG.Arm.isa := (p224CombWith u).comb

def mulGeneratorP224 : Prog VG.Arm.isa := mulGeneratorP224With false

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

def signP224CombWith (u : Bool) : Prog VG.Arm.isa :=
  (p224With u).signWith (Weierstrass.Arm.mulGeneratorP224With u)

def signP224Comb : Prog VG.Arm.isa := signP224CombWith false

def signP224CombU : Prog VG.Arm.isa := signP224CombWith true

def publicKeyP224CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (p224With u) (Weierstrass.Arm.mulGeneratorP224With u)

def publicKeyP224Comb : Prog VG.Arm.isa := publicKeyP224CombWith false

def publicKeyP224CombU : Prog VG.Arm.isa := publicKeyP224CombWith true

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_p224_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorP224With (u : Bool) : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (p224.sl K) (bitsAt p224.n 0) (8 * p224.n)) (Weierstrass.Arm.mulGeneratorP224With u)

def verifyGeneratorP224 : Prog VG.Arm.isa := verifyGeneratorP224With false

def verifyP224CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (p224With u) (verifyGeneratorP224With u)

def verifyP224Comb : Prog VG.Arm.isa := verifyP224CombWith false

def verifyP224CombU : Prog VG.Arm.isa := verifyP224CombWith true

end VG.Impl.Ecdsa.Arm
