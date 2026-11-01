module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over brainpoolP512r1 on PPC64LE: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- brainpoolP512r1 as the code has it. -/
def brainpoolp512r1 : Cfg := ⟨8, Spec.BrainpoolP512r1.curve, Impl.Weierstrass.Mont.brainpoolp512r1p, Impl.Weierstrass.Mont.brainpoolp512r1n, none⟩

/-- `vg_ecdsa_brainpoolp512r1_sign`. -/
def signBrainpoolP512r1 : Prog isa := brainpoolp512r1.sign

end VG.Impl.Ecdsa.PPC64LE
