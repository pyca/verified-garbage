module

public import VerifiedGarbage.Impl.Ecdsa.Arm
public import VerifiedGarbage.Spec.BrainpoolP512r1

/-! # ECDSA over brainpoolP512r1 on 32-bit ARM: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- brainpoolP512r1 as the code has it. -/
def brainpoolp512r1 : Cfg := ⟨8, Spec.BrainpoolP512r1.curve, Spec.Weierstrass.Mont.brainpoolp512r1p, Spec.Weierstrass.Mont.brainpoolp512r1n⟩

end VG.Impl.Ecdsa.Arm
