module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Impl.Ecdsa.P256.Arm
public import VerifiedGarbage.Impl.P256.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! # P-256's generator by the shared signed seven-bit comb on 32-bit ARM

The comb of `TComb.lean` with P-256's tables (`Impl/P256/CombTable7.lean`, the
x86-64 comb's), and signing, public-key derivation and verification with it
in place of the ladder for `[k]G`. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

/-- The comb, its point additions by `vg_p256_point_add_umaal` if `u`. -/
def p256CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.p256With u
  let start := VG.Impl.P256.p256Comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 37, tsym := "VG_P256_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x, u := u }

def p256Comb : TCombCfg := p256CombWith false

@[irreducible] def p256CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 4 (2^256) VG.Spec.P256.curve.p VG.Impl.P256.p256Comb7

def p256CombConsts : List (String × List (BitVec 64)) :=
  [(p256Comb.tsym,p256CombWords)]

def mulGeneratorP256With (u : Bool) : Prog VG.Arm.isa := (p256CombWith u).comb

def mulGeneratorP256 : Prog VG.Arm.isa := mulGeneratorP256With false

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

def signP256CombWith (u : Bool) : Prog VG.Arm.isa :=
  (p256With u).signWith (Weierstrass.Arm.mulGeneratorP256With u)

def signP256Comb : Prog VG.Arm.isa := signP256CombWith false

def signP256CombU : Prog VG.Arm.isa := signP256CombWith true

def publicKeyP256CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (p256With u) (Weierstrass.Arm.mulGeneratorP256With u)

def publicKeyP256Comb : Prog VG.Arm.isa := publicKeyP256CombWith false

def publicKeyP256CombU : Prog VG.Arm.isa := publicKeyP256CombWith true

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_p256_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorP256With (u : Bool) : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (p256.sl K) (bitsAt p256.n 0) (8 * p256.n)) (Weierstrass.Arm.mulGeneratorP256With u)

def verifyGeneratorP256 : Prog VG.Arm.isa := verifyGeneratorP256With false

def verifyP256CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (p256With u) (verifyGeneratorP256With u)

def verifyP256Comb : Prog VG.Arm.isa := verifyP256CombWith false

def verifyP256CombU : Prog VG.Arm.isa := verifyP256CombWith true

end VG.Impl.Ecdsa.Arm
