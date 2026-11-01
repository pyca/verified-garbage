module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over brainpoolP384r1 on PPC64LE: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- brainpoolP384r1 as the code has it. -/
def brainpoolp384r1 : Cfg := ⟨6, Spec.BrainpoolP384r1.curve, Impl.Weierstrass.Mont.brainpoolp384r1p, Impl.Weierstrass.Mont.brainpoolp384r1n, none⟩

/-- `vg_ecdsa_brainpoolp384r1_sign`. -/
def signBrainpoolP384r1 : Prog isa := brainpoolp384r1.sign

end VG.Impl.Ecdsa.PPC64LE
