import VerifiedGarbage.Impl.Ecdsa.X86
import VerifiedGarbage.Spec.P521

/-! # ECDSA over P-521 on x86 (32-bit): nine-word field elements and scalars -/

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-521 as the code has it. -/
def p521 : Cfg := { n := 9, C := Spec.P521.curve }

/-- `vg_ecdsa_p521_sign`. -/
def signP521 : Prog isa := p521.sign

end VG.Impl.Ecdsa.X86
