import VerifiedGarbage.Impl.Ecdsa.X86
import VerifiedGarbage.Spec.P384

/-! # ECDSA over P-384 on x86 (32-bit): six-word field elements and scalars -/

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-384 as the code has it. -/
def p384 : Cfg := ⟨6, Spec.P384.curve⟩

/-- `vg_ecdsa_p384_sign`. -/
def signP384 : Prog isa := p384.sign

end VG.Impl.Ecdsa.X86
