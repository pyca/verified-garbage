import VerifiedGarbage.Impl.Ecdsa.X86_64
import VerifiedGarbage.Spec.P224
import VerifiedGarbage.Impl.P224.CombTable7

/-! # ECDSA over P-224 on x86-64: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

/-- P-224 as the code has it. -/
def p224 : Cfg where
  n := 4
  C := Spec.P224.curve
  comb := some ⟨7, Impl.P224.p224Comb7, Impl.P224.p224Comb7Start, "VG_P224_COMB", false⟩

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

end VG.Impl.Ecdsa.X86_64
