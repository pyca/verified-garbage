import VerifiedGarbage.Impl.Ecdsa.X86
import VerifiedGarbage.Spec.P224

/-! # ECDSA over P-224 on x86 (32-bit): four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-224 as the code has it. -/
def p224 : Cfg := ⟨4, Spec.P224.curve⟩

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

end VG.Impl.Ecdsa.X86
