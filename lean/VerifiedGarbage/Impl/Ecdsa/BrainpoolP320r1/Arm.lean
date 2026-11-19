module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over brainpoolP320r1 on 32-bit ARM: five-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- brainpoolP320r1 as the code has it, its field multiplications by
`vg_brainpoolp320r1_mul_mod_<p|n>_umaal` if `u`. -/
def brainpoolp320r1With (u : Bool) : Cfg :=
  ⟨5, Spec.BrainpoolP320r1.curve, Impl.Weierstrass.Mont.brainpoolp320r1p, Impl.Weierstrass.Mont.brainpoolp320r1n,
    some Impl.Weierstrass.Mul.brainpoolp320r1, u⟩

/-- brainpoolP320r1 as the code has it. -/
def brainpoolp320r1 : Cfg := brainpoolp320r1With false

/-- `vg_ecdsa_brainpoolp320r1_sign`. -/
def signBrainpoolP320r1 : Prog isa := brainpoolp320r1.sign

/-- `vg_brainpoolp320r1_mul`, or with `u` `vg_brainpoolp320r1_mul_umaal`. -/
def mulBrainpoolP320r1With (u : Bool) : Prog isa := (brainpoolp320r1With u).mulFn

/-- `vg_brainpoolp320r1_mul`. -/
def mulBrainpoolP320r1 : Prog isa := mulBrainpoolP320r1With false

/-- `vg_brainpoolp320r1_mul_umaal`. -/
def mulBrainpoolP320r1U : Prog isa := mulBrainpoolP320r1With true

/-- `vg_brainpoolp320r1_mul_public`, or with `u` `vg_brainpoolp320r1_mul_public_umaal`. -/
def mulPubBrainpoolP320r1With (u : Bool) : Prog isa := (brainpoolp320r1With u).pubFn

/-- `vg_brainpoolp320r1_mul_public`. -/
def mulPubBrainpoolP320r1 : Prog isa := mulPubBrainpoolP320r1With false

/-- `vg_brainpoolp320r1_mul_public_umaal`. -/
def mulPubBrainpoolP320r1U : Prog isa := mulPubBrainpoolP320r1With true

end VG.Impl.Ecdsa.Arm
