module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over brainpoolP384r1 on 32-bit ARM: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- brainpoolP384r1 as the code has it, its field multiplications by
`vg_brainpoolp384r1_mul_mod_<p|n>_umaal` if `u`. -/
def brainpoolp384r1With (u : Bool) : Cfg :=
  ⟨6, Spec.BrainpoolP384r1.curve, Impl.Weierstrass.Mont.brainpoolp384r1p, Impl.Weierstrass.Mont.brainpoolp384r1n, none, u⟩

/-- brainpoolP384r1 as the code has it. -/
def brainpoolp384r1 : Cfg := brainpoolp384r1With false

/-- `vg_ecdsa_brainpoolp384r1_sign`, or with `u` `vg_ecdsa_brainpoolp384r1_sign_umaal`. -/
def signBrainpoolP384r1With (u : Bool) : Prog isa := (brainpoolp384r1With u).sign

/-- `vg_ecdsa_brainpoolp384r1_sign`. -/
def signBrainpoolP384r1 : Prog isa := signBrainpoolP384r1With false

/-- `vg_ecdsa_brainpoolp384r1_sign_umaal`. -/
def signBrainpoolP384r1U : Prog isa := signBrainpoolP384r1With true

end VG.Impl.Ecdsa.Arm
