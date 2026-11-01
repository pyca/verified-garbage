module

public import VerifiedGarbage.Impl.Ecdsa.X86

/-! # ECDSA over brainpoolP384r1 on x86 (32-bit): six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- brainpoolP384r1 as the code has it. -/
def brainpoolp384r1 : Cfg where
  n := 6
  C := Spec.BrainpoolP384r1.curve
  SP := Impl.Weierstrass.Mont.brainpoolp384r1p
  SN := Impl.Weierstrass.Mont.brainpoolp384r1n

/-- `vg_ecdsa_brainpoolp384r1_sign`. -/
def signBrainpoolP384r1 : Prog isa := brainpoolp384r1.sign

end VG.Impl.Ecdsa.X86
