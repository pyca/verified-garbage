import VerifiedGarbage.Impl.Ecdsa.X86_64
import VerifiedGarbage.Spec.P521
import VerifiedGarbage.Impl.P521.CombTable7

/-! # ECDSA over P-521 on x86-64: nine-word field elements and scalars -/

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

/-- P-521 as the code has it. -/
def p521 : Cfg where
  n := 9
  C := Spec.P521.curve
  comb := some ⟨7, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB", false⟩

/-- `vg_ecdsa_p521_sign`. -/
def signP521 : Prog isa := p521.sign

end VG.Impl.Ecdsa.X86_64
