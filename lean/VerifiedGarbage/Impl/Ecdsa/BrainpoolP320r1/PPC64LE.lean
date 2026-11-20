module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over brainpoolP320r1 on PPC64LE: five-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- brainpoolP320r1 as the code has it. -/
def brainpoolp320r1 : Cfg := ⟨5, Spec.BrainpoolP320r1.curve, Impl.Weierstrass.Mont.brainpoolp320r1p, Impl.Weierstrass.Mont.brainpoolp320r1n, none⟩


end VG.Impl.Ecdsa.PPC64LE
