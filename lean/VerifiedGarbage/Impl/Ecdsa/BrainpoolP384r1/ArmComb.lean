module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.Arm
public import VerifiedGarbage.Impl.BrainpoolP384r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! # brainpoolP384r1's generator by the shared signed seven-bit comb on 32-bit ARM

The comb of `TComb.lean` with brainpoolP384r1's tables (`Impl/BrainpoolP384r1/CombTable7.lean`), and signing, public-key derivation and verification with it
in place of the ladder for `[k]G`. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

/-- The comb, its point additions by `vg_brainpoolp384r1_point_add_umaal` if `u`. -/
def brainpoolp384r1CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.brainpoolp384r1With u
  let start := VG.Impl.BrainpoolP384r1.comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 55, tsym := "VG_BRAINPOOLP384R1_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x, u := u }

def brainpoolp384r1Comb : TCombCfg := brainpoolp384r1CombWith false

@[irreducible] def brainpoolp384r1CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 6 (2^384) VG.Spec.BrainpoolP384r1.curve.p VG.Impl.BrainpoolP384r1.comb7

def brainpoolp384r1CombConsts : List (String × List (BitVec 64)) :=
  [(brainpoolp384r1Comb.tsym,brainpoolp384r1CombWords)]

def mulGeneratorBrainpoolP384r1With (u : Bool) : Prog VG.Arm.isa := (brainpoolp384r1CombWith u).comb

def mulGeneratorBrainpoolP384r1 : Prog VG.Arm.isa := mulGeneratorBrainpoolP384r1With false

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

def signBrainpoolP384r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  (brainpoolp384r1With u).signWith (Weierstrass.Arm.mulGeneratorBrainpoolP384r1With u)

def signBrainpoolP384r1Comb : Prog VG.Arm.isa := signBrainpoolP384r1CombWith false

def signBrainpoolP384r1CombU : Prog VG.Arm.isa := signBrainpoolP384r1CombWith true

def publicKeyBrainpoolP384r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (brainpoolp384r1With u) (Weierstrass.Arm.mulGeneratorBrainpoolP384r1With u)

def publicKeyBrainpoolP384r1Comb : Prog VG.Arm.isa := publicKeyBrainpoolP384r1CombWith false

def publicKeyBrainpoolP384r1CombU : Prog VG.Arm.isa := publicKeyBrainpoolP384r1CombWith true

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_brainpoolp384r1_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorBrainpoolP384r1With (u : Bool) : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (brainpoolp384r1.sl K) (bitsAt brainpoolp384r1.n 0) (8 * brainpoolp384r1.n)) (Weierstrass.Arm.mulGeneratorBrainpoolP384r1With u)

def verifyBrainpoolP384r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (brainpoolp384r1With u) (verifyGeneratorBrainpoolP384r1With u)

def verifyBrainpoolP384r1Comb : Prog VG.Arm.isa := verifyBrainpoolP384r1CombWith false

def verifyBrainpoolP384r1CombU : Prog VG.Arm.isa := verifyBrainpoolP384r1CombWith true

end VG.Impl.Ecdsa.Arm
