module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over brainpoolP256r1 on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- brainpoolP256r1 as the code has it. -/
def brainpoolp256r1 : Cfg := ⟨4, Spec.BrainpoolP256r1.curve, Impl.Weierstrass.Mont.brainpoolp256r1p, Impl.Weierstrass.Mont.brainpoolp256r1n, none⟩

/-- `vg_ecdsa_brainpoolp256r1_sign`. -/
def signBrainpoolP256r1 : Prog isa := brainpoolp256r1.sign

end VG.Impl.Ecdsa.PPC64LE
