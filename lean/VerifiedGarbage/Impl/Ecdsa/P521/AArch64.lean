import VerifiedGarbage.Impl.Ecdsa.AArch64
import VerifiedGarbage.Spec.P521
import VerifiedGarbage.Impl.P521.CombTable7

/-! # ECDSA over P-521 on AArch64: nine-word field elements and scalars -/

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- P-521 as the code has it. -/
def p521 : Cfg := ⟨9, Spec.P521.curve, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB", false⟩

/-- `vg_ecdsa_p521_sign`. -/
def signP521 : Prog isa := p521.sign

end VG.Impl.Ecdsa.AArch64
