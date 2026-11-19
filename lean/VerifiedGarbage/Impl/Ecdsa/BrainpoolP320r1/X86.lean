module

public import VerifiedGarbage.Impl.Ecdsa.X86

/-! # ECDSA over brainpoolP320r1 on x86 (32-bit): five-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- brainpoolP320r1 as the code has it. -/
def brainpoolp320r1 : Cfg where
  n := 5
  C := Spec.BrainpoolP320r1.curve
  SP := Impl.Weierstrass.Mont.brainpoolp320r1p
  SN := Impl.Weierstrass.Mont.brainpoolp320r1n

end VG.Impl.Ecdsa.X86
