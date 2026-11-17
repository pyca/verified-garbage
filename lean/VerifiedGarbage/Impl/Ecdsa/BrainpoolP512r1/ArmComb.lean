module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombI
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm
public import VerifiedGarbage.Impl.BrainpoolP512r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! # brainpoolP512r1's generator by the signed seven-bit comb on 32-bit ARM

The comb with the addition inlined (`Impl/Weierstrass/Arm/TCombI.lean`;
brainpoolP512r1's eight-word coordinates do not fit the point functions')
with brainpoolP512r1's tables (`Impl/BrainpoolP512r1/CombTable7.lean`, the
other targets'): 74 windows of seven bits over the ladder's table of the
scalar's 512 bits. Signing, public-key derivation and verification with it
in place of the ladder for `[k]G`. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

/-- The comb, on the signature's layout: the ladder's `R`, `a`, `3b` and
table of bits, the entry in the ladder's `T`, the sum in its `D`, `-y` in
`D`'s `x` before it, and zero at `ZERO`; its field multiplications by
`vg_brainpoolp512r1_mul_mod_p_umaal` if `u`. -/
def brainpoolp512r1CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.brainpoolp512r1With u
  let start := VG.Impl.BrainpoolP512r1.comb7Start
  { L := c.ladderCfg, F := c.SP, w := 7, J := 74, tsym := "VG_BRAINPOOLP512R1_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.sl VG.Impl.Ecdsa.Arm.DX, u := u
    qBase := c.sl VG.Impl.Ecdsa.Arm.TX }

def brainpoolp512r1Comb : TCombCfg := brainpoolp512r1CombWith false

/-- The table's words, in Montgomery's form. -/
@[irreducible] def brainpoolp512r1CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 8 (2^512) VG.Spec.BrainpoolP512r1.curve.p VG.Impl.BrainpoolP512r1.comb7

def brainpoolp512r1CombConsts : List (String × List (BitVec 64)) :=
  [(brainpoolp512r1Comb.tsym,brainpoolp512r1CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorBrainpoolP512r1With (u : Bool) : Prog VG.Arm.isa := (brainpoolp512r1CombWith u).combI

def mulGeneratorBrainpoolP512r1 : Prog VG.Arm.isa := mulGeneratorBrainpoolP512r1With false

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

/-- `vg_ecdsa_brainpoolp512r1_sign`, or with `u` `vg_ecdsa_brainpoolp512r1_sign_umaal`, with `[k]G` by the comb. -/
def signBrainpoolP512r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  (brainpoolp512r1With u).signWith (Weierstrass.Arm.mulGeneratorBrainpoolP512r1With u)

def signBrainpoolP512r1Comb : Prog VG.Arm.isa := signBrainpoolP512r1CombWith false

def signBrainpoolP512r1CombU : Prog VG.Arm.isa := signBrainpoolP512r1CombWith true

/-- `vg_ec_brainpoolp512r1_public_key`, or with `u` its `_umaal` variant, with `[d]G` by the comb. -/
def publicKeyBrainpoolP512r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (brainpoolp512r1With u) (Weierstrass.Arm.mulGeneratorBrainpoolP512r1With u)

def publicKeyBrainpoolP512r1Comb : Prog VG.Arm.isa := publicKeyBrainpoolP512r1CombWith false

def publicKeyBrainpoolP512r1CombU : Prog VG.Arm.isa := publicKeyBrainpoolP512r1CombWith true

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_brainpoolp512r1_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorBrainpoolP512r1With (u : Bool) : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (brainpoolp512r1.sl K) (bitsAt brainpoolp512r1.n 0) (8 * brainpoolp512r1.n)) (Weierstrass.Arm.mulGeneratorBrainpoolP512r1With u)

/-- `vg_ecdsa_brainpoolp512r1_verify`, or with `u` its `_umaal` variant, with `[u₁]G` by the comb. -/
def verifyBrainpoolP512r1CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (brainpoolp512r1With u) (verifyGeneratorBrainpoolP512r1With u)

def verifyBrainpoolP512r1Comb : Prog VG.Arm.isa := verifyBrainpoolP512r1CombWith false

def verifyBrainpoolP512r1CombU : Prog VG.Arm.isa := verifyBrainpoolP512r1CombWith true

end VG.Impl.Ecdsa.Arm
