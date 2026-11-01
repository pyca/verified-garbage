module

public import VerifiedGarbage.Impl.Ecdsa.X86

/-! # ECDSA over brainpoolP512r1 on x86 (32-bit): eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- brainpoolP512r1 as the code has it. -/
def brainpoolp512r1 : Cfg where
  n := 8
  C := Spec.BrainpoolP512r1.curve
  SP := Impl.Weierstrass.Mont.brainpoolp512r1p
  SN := Impl.Weierstrass.Mont.brainpoolp512r1n

/-- `vg_ecdsa_brainpoolp512r1_sign`. -/
def signBrainpoolP512r1 : Prog isa := brainpoolp512r1.sign

end VG.Impl.Ecdsa.X86
