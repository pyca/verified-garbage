module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.Arm
public import VerifiedGarbage.Impl.BrainpoolP256r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! # brainpoolP256r1's generator by the shared signed seven-bit comb on 32-bit ARM

The comb of `TComb.lean` with brainpoolP256r1's tables (`Impl/BrainpoolP256r1/CombTable7.lean`), and signing, public-key derivation and verification with it
in place of the ladder for `[k]G`. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

/-- The comb, its point additions by `vg_brainpoolp256r1_point_add_umaal` if `u`. -/
def brainpoolp256r1CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.brainpoolp256r1With u
  let start := VG.Impl.BrainpoolP256r1.comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 37, tsym := "VG_BRAINPOOLP256R1_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.ladderCfg.T.x, u := u }

def brainpoolp256r1Comb : TCombCfg := brainpoolp256r1CombWith false

@[irreducible] def brainpoolp256r1CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 4 (2^256) VG.Spec.BrainpoolP256r1.curve.p VG.Impl.BrainpoolP256r1.comb7

def brainpoolp256r1CombConsts : List (String × List (BitVec 64)) :=
  [(brainpoolp256r1Comb.tsym,brainpoolp256r1CombWords)]

def mulGeneratorBrainpoolP256r1With (u : Bool) : Prog VG.Arm.isa := (brainpoolp256r1CombWith u).comb

def mulGeneratorBrainpoolP256r1 : Prog VG.Arm.isa := mulGeneratorBrainpoolP256r1With false

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

def signBrainpoolP256r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  (brainpoolp256r1With u).signWith (Weierstrass.Arm.mulGeneratorBrainpoolP256r1With u)

def signBrainpoolP256r1Comb : Prog VG.Arm.isa := signBrainpoolP256r1CombWith false

def signBrainpoolP256r1CombU : Prog VG.Arm.isa := signBrainpoolP256r1CombWith true

def publicKeyBrainpoolP256r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (brainpoolp256r1With u) (Weierstrass.Arm.mulGeneratorBrainpoolP256r1With u)

def publicKeyBrainpoolP256r1Comb : Prog VG.Arm.isa := publicKeyBrainpoolP256r1CombWith false

def publicKeyBrainpoolP256r1CombU : Prog VG.Arm.isa := publicKeyBrainpoolP256r1CombWith true

def verifyBrainpoolP256r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (brainpoolp256r1With u) (Weierstrass.Arm.mulGeneratorBrainpoolP256r1With u)

def verifyBrainpoolP256r1Comb : Prog VG.Arm.isa := verifyBrainpoolP256r1CombWith false

def verifyBrainpoolP256r1CombU : Prog VG.Arm.isa := verifyBrainpoolP256r1CombWith true

end VG.Impl.Ecdsa.Arm
