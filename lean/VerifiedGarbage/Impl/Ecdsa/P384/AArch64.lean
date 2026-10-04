import VerifiedGarbage.Impl.Ecdsa.AArch64
import VerifiedGarbage.Spec.P384
import VerifiedGarbage.Impl.P384.CombTable

/-! # ECDSA over P-384 on AArch64: six-word field elements and scalars -/

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- P-384 as the code has it. -/
def p384 : Cfg := ⟨6, Spec.P384.curve, Impl.P384.p384Comb, Impl.P384.p384CombStart⟩

/-- `vg_ecdsa_p384_sign`. -/
def signP384 : Prog isa := p384.sign

end VG.Impl.Ecdsa.AArch64
