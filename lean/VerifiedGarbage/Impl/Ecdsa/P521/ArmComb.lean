module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombI
public import VerifiedGarbage.Impl.Ecdsa.P521.Arm
public import VerifiedGarbage.Impl.P521.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! # P-521's generator by the signed seven-bit comb on 32-bit ARM

The comb with the addition inlined (`Impl/Weierstrass/Arm/TCombI.lean`;
P-521's nine-word coordinates do not fit the point functions') with P-521's
tables (`Impl/P521/CombTable7.lean`, the other targets'): 83 windows of
seven bits over the ladder's table of the scalar's bits, all `64 n = 576` of
them. Signing, public-key derivation and verification with it in place of
the call of `vg_p521_mul` for `[k]G`. -/

@[expose] public section
namespace VG.Impl.Weierstrass.Arm

/-- The comb, on the signature's layout: the ladder's `R`, `a`, `3b` and
table of bits (of 576 bits), the entry in the ladder's `T`, the sum in its
`D`, `-y` in `D`'s `x` before it, and zero at `ZERO`; its field
multiplications by `vg_p521_mul_mod_p_umaal` if `u`. -/
def p521CombWith (u : Bool) : TCombCfg :=
  let c := VG.Impl.Ecdsa.Arm.p521With u
  let start := VG.Impl.P521.p521Comb7Start
  { L := { c.ladderCfg with nbits := 64 * c.n }, F := c.SP, w := 7, J := 83, tsym := "VG_P521_COMB"
    start := (c.mont start.1,c.mont start.2)
    one := c.R%c.C.p, zero := c.sl VG.Impl.Ecdsa.Arm.ZERO, neg := c.sl VG.Impl.Ecdsa.Arm.DX, u := u
    qBase := c.sl VG.Impl.Ecdsa.Arm.TX }

def p521Comb : TCombCfg := p521CombWith false

/-- The table's words, in Montgomery's form. -/
@[irreducible] def p521CombWords : List (BitVec 64) :=
  VG.Impl.Weierstrass.tcombWords 9 (2^576) VG.Spec.P521.curve.p VG.Impl.P521.p521Comb7

def p521CombConsts : List (String × List (BitVec 64)) :=
  [(p521Comb.tsym,p521CombWords)]

/-- `R = [k]G` by the comb. -/
def mulGeneratorP521With (u : Bool) : Prog VG.Arm.isa := (p521CombWith u).combI

def mulGeneratorP521 : Prog VG.Arm.isa := mulGeneratorP521With false

end VG.Impl.Weierstrass.Arm

namespace VG.Impl.Ecdsa.Arm

/-- `vg_ecdsa_p521_sign`, or with `u` `vg_ecdsa_p521_sign_umaal`, with `[k]G` by the comb. -/
def signP521CombWith (u : Bool) : Prog VG.Arm.isa :=
  (p521With u).signWith (Weierstrass.Arm.mulGeneratorP521With u)

def signP521Comb : Prog VG.Arm.isa := signP521CombWith false

def signP521CombU : Prog VG.Arm.isa := signP521CombWith true

/-- `vg_ec_p521_public_key`, or with `u` its `_umaal` variant, with `[d]G` by the comb. -/
def publicKeyP521CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (p521With u) (Weierstrass.Arm.mulGeneratorP521With u)

def publicKeyP521Comb : Prog VG.Arm.isa := publicKeyP521CombWith false

def publicKeyP521CombU : Prog VG.Arm.isa := publicKeyP521CombWith true

/-- Verification's `[u]G`: `u` is in `K`'s slot, where `vg_p521_mul` reads it
(`Verify.Arm.Cfg.scalarAt`), so the table of its bits that the comb reads
is made from it first. -/
def verifyGeneratorP521With (u : Bool) : Prog VG.Arm.isa :=
  .seq (Weierstrass.Arm.bits (p521.sl K) (bitsAt p521.n 0) (8 * p521.n)) (Weierstrass.Arm.mulGeneratorP521With u)

/-- `vg_ecdsa_p521_verify`, or with `u` its `_umaal` variant, with `[u₁]G` by the comb. -/
def verifyP521CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (p521With u) (verifyGeneratorP521With u)

def verifyP521Comb : Prog VG.Arm.isa := verifyP521CombWith false

def verifyP521CombU : Prog VG.Arm.isa := verifyP521CombWith true

end VG.Impl.Ecdsa.Arm
