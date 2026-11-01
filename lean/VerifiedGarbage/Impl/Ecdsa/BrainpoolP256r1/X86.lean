module

public import VerifiedGarbage.Impl.Ecdsa.X86

/-! # ECDSA over brainpoolP256r1 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- brainpoolP256r1 as the code has it. -/
def brainpoolp256r1 : Cfg where
  n := 4
  C := Spec.BrainpoolP256r1.curve
  SP := Impl.Weierstrass.Mont.brainpoolp256r1p
  SN := Impl.Weierstrass.Mont.brainpoolp256r1n

/-- `vg_ecdsa_brainpoolp256r1_sign`. -/
def signBrainpoolP256r1 : Prog isa := brainpoolp256r1.sign

end VG.Impl.Ecdsa.X86
