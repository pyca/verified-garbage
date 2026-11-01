module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over brainpoolP256r1 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- brainpoolP256r1 as the code has it, its field multiplications by
`vg_brainpoolp256r1_mul_mod_<p|n>_umaal` if `u`. -/
def brainpoolp256r1With (u : Bool) : Cfg :=
  ⟨4, Spec.BrainpoolP256r1.curve, Impl.Weierstrass.Mont.brainpoolp256r1p, Impl.Weierstrass.Mont.brainpoolp256r1n, none, u⟩

/-- brainpoolP256r1 as the code has it. -/
def brainpoolp256r1 : Cfg := brainpoolp256r1With false

/-- `vg_ecdsa_brainpoolp256r1_sign`. -/
def signBrainpoolP256r1 : Prog isa := brainpoolp256r1.sign

end VG.Impl.Ecdsa.Arm
