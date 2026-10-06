import VerifiedGarbage.Impl.Ecdsa.X86
import VerifiedGarbage.Spec.P192

/-! # ECDSA over P-192 on x86 (32-bit): three-word field elements and scalars -/

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-192 as the code has it. -/
def p192 : Cfg := ⟨3, Spec.P192.curve⟩

/-- `vg_ecdsa_p192_sign`. -/
def signP192 : Prog isa := p192.sign

end VG.Impl.Ecdsa.X86
