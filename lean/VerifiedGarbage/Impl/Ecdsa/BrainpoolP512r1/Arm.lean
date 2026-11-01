module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over brainpoolP512r1 on 32-bit ARM: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- brainpoolP512r1 as the code has it, its field multiplications by
`vg_brainpoolp512r1_mul_mod_<p|n>_umaal` if `u`. -/
def brainpoolp512r1With (u : Bool) : Cfg :=
  ⟨8, Spec.BrainpoolP512r1.curve, Impl.Weierstrass.Mont.brainpoolp512r1p, Impl.Weierstrass.Mont.brainpoolp512r1n, none, u⟩

/-- brainpoolP512r1 as the code has it. -/
def brainpoolp512r1 : Cfg := brainpoolp512r1With false

/-- `vg_ecdsa_brainpoolp512r1_sign`. -/
def signBrainpoolP512r1With (u : Bool) : Prog isa := (brainpoolp512r1With u).sign

def signBrainpoolP512r1 : Prog isa := signBrainpoolP512r1With false

/-- `vg_ecdsa_brainpoolp512r1_sign_umaal`. -/
def signBrainpoolP512r1U : Prog isa := signBrainpoolP512r1With true

end VG.Impl.Ecdsa.Arm
