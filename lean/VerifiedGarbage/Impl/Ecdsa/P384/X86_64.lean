module

public import VerifiedGarbage.Impl.Ecdsa.X86_64
public import VerifiedGarbage.Spec.P384
public import VerifiedGarbage.Impl.P384.CombTable7

/-! # ECDSA over P-384 on x86-64: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

/-- P-384 as the code has it. -/
def p384 : Cfg where
  n := 6
  C := Spec.P384.curve
  comb := some ⟨7, Impl.P384.p384Comb7, Impl.P384.p384Comb7Start, "VG_P384_COMB", false⟩
  fastN := true

/-- `vg_ecdsa_p384_sign`. -/
def signP384 : Prog isa := p384.sign

/-- P-384 multiplying modulo `p` and `n` with BMI2 and ADX (`Mod.adx`), and
selecting the comb's entries with AVX2 (`Cfg.avx2`). -/
def p384x : Cfg := { p384 with adx := true, avx2 := true }

/-- `vg_ecdsa_p384_sign_adx`. -/
def signP384Adx : Prog isa := p384x.sign

end VG.Impl.Ecdsa.X86_64
