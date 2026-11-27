module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.Arm
public import VerifiedGarbage.Impl.BrainpoolP320r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! # brainpoolP320r1's generator by the shared signed seven-bit comb on 32-bit ARM

The comb of `TComb.lean` with brainpoolP320r1's tables (`Impl/BrainpoolP320r1/CombTable7.lean`), and signing, public-key derivation and verification with it
in place of the ladder for `[k]G`. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

/-- The comb, its point additions by `vg_brainpoolp320r1_point_add_umaal` if `u`. -/
def brainpoolp320r1CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.brainpoolp320r1With u
  let start := VG.Impl.BrainpoolP320r1.comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 46, tsym := "VG_BRAINPOOLP320R1_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x, u := u }

def brainpoolp320r1Comb : TCombCfg := brainpoolp320r1CombWith false

@[irreducible] def brainpoolp320r1CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 5 (2^320) VG.Spec.BrainpoolP320r1.curve.p VG.Impl.BrainpoolP320r1.comb7

def brainpoolp320r1CombConsts : List (String × List (BitVec 64)) :=
  [(brainpoolp320r1Comb.tsym,brainpoolp320r1CombWords)]

def mulGeneratorBrainpoolP320r1With (u : Bool) : Prog VG.Arm.isa := (brainpoolp320r1CombWith u).comb

def mulGeneratorBrainpoolP320r1 : Prog VG.Arm.isa := mulGeneratorBrainpoolP320r1With false

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

def signBrainpoolP320r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  (brainpoolp320r1With u).signWith (Weierstrass.Arm.mulGeneratorBrainpoolP320r1With u)

def signBrainpoolP320r1Comb : Prog VG.Arm.isa := signBrainpoolP320r1CombWith false

def signBrainpoolP320r1CombU : Prog VG.Arm.isa := signBrainpoolP320r1CombWith true

def publicKeyBrainpoolP320r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (brainpoolp320r1With u) (Weierstrass.Arm.mulGeneratorBrainpoolP320r1With u)

def publicKeyBrainpoolP320r1Comb : Prog VG.Arm.isa := publicKeyBrainpoolP320r1CombWith false

def publicKeyBrainpoolP320r1CombU : Prog VG.Arm.isa := publicKeyBrainpoolP320r1CombWith true

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_brainpoolp320r1_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorBrainpoolP320r1With (u : Bool) : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (brainpoolp320r1.sl K) (bitsAt brainpoolp320r1.n 0) (8 * brainpoolp320r1.n)) (Weierstrass.Arm.mulGeneratorBrainpoolP320r1With u)

def verifyBrainpoolP320r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (brainpoolp320r1With u) (verifyGeneratorBrainpoolP320r1With u)

def verifyBrainpoolP320r1Comb : Prog VG.Arm.isa := verifyBrainpoolP320r1CombWith false

def verifyBrainpoolP320r1CombU : Prog VG.Arm.isa := verifyBrainpoolP320r1CombWith true

end VG.Impl.Ecdsa.Arm
