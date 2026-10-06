import VerifiedGarbage.Impl.Ecdsa.X86_64
import VerifiedGarbage.Spec.P256
import VerifiedGarbage.Impl.P256.CombTable7

/-! # ECDSA over P-256 on x86-64: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

/-- P-256 as the code has it. -/
def p256 : Cfg where
  n := 4
  C := Spec.P256.curve
  comb := some ⟨7, Impl.P256.p256Comb7, Impl.P256.p256Comb7Start, "VG_P256_COMB"⟩
  fastN := true

/-- P-256, multiplying with BMI2 and ADX. -/
def p256x : Cfg := { p256 with adx := true }

/-- `vg_ecdsa_p256_sign`. -/
def signP256 : Prog isa := p256.sign

/-- `vg_ecdsa_p256_sign_adx`. -/
def signP256Adx : Prog isa := p256x.sign

end VG.Impl.Ecdsa.X86_64
