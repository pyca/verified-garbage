module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over brainpoolP512r1 on 32-bit ARM: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- brainpoolP512r1 as the code has it, its field multiplications by
`vg_brainpoolp512r1_mul_mod_<p|n>_umaal` if `u`. -/
def brainpoolp512r1With (u : Bool) : Cfg :=
  ⟨8, Spec.BrainpoolP512r1.curve, Impl.Weierstrass.Mont.brainpoolp512r1p, Impl.Weierstrass.Mont.brainpoolp512r1n,
    some Impl.Weierstrass.Mul.brainpoolp512r1, u⟩

/-- brainpoolP512r1 as the code has it. -/
def brainpoolp512r1 : Cfg := brainpoolp512r1With false

/-- `vg_ecdsa_brainpoolp512r1_sign`. -/
def signBrainpoolP512r1 : Prog isa := brainpoolp512r1.sign

/-- `vg_brainpoolp512r1_mul`, or with `u` `vg_brainpoolp512r1_mul_umaal`. -/
def mulBrainpoolP512r1With (u : Bool) : Prog isa := (brainpoolp512r1With u).mulFn

/-- `vg_brainpoolp512r1_mul`. -/
def mulBrainpoolP512r1 : Prog isa := mulBrainpoolP512r1With false

/-- `vg_brainpoolp512r1_mul_umaal`. -/
def mulBrainpoolP512r1U : Prog isa := mulBrainpoolP512r1With true

/-- `vg_brainpoolp512r1_mul_public`, or with `u` `vg_brainpoolp512r1_mul_public_umaal`. -/
def mulPubBrainpoolP512r1With (u : Bool) : Prog isa := (brainpoolp512r1With u).pubFn

/-- `vg_brainpoolp512r1_mul_public`. -/
def mulPubBrainpoolP512r1 : Prog isa := mulPubBrainpoolP512r1With false

/-- `vg_brainpoolp512r1_mul_public_umaal`. -/
def mulPubBrainpoolP512r1U : Prog isa := mulPubBrainpoolP512r1With true

end VG.Impl.Ecdsa.Arm
