import VerifiedGarbage.Impl.Ecdsa.X86_64
import VerifiedGarbage.Spec.P384

/-! # ECDSA over P-384 on x86-64: six-word field elements and scalars -/

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

/-- P-384 as the code has it. -/
def p384 : Cfg := ⟨6, Spec.P384.curve⟩

/-- `vg_ecdsa_p384_sign`. -/
def signP384 : Prog isa := p384.sign

end VG.Impl.Ecdsa.X86_64
