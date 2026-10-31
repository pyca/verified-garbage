module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over brainpoolP384r1 on 32-bit ARM: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- brainpoolP384r1 as the code has it. -/
def brainpoolp384r1 : Cfg := ⟨6, Spec.BrainpoolP384r1.curve, Spec.Weierstrass.Mont.brainpoolp384r1p, Spec.Weierstrass.Mont.brainpoolp384r1n, none, false⟩

/-- `vg_ecdsa_brainpoolp384r1_sign`. -/
def signBrainpoolP384r1 : Prog isa := brainpoolp384r1.sign

end VG.Impl.Ecdsa.Arm
