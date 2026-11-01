module

public import VerifiedGarbage.Impl.Ecdsa.X86_64
public import VerifiedGarbage.Impl.P224.CombTable7

/-! # ECDSA over P-224 on x86-64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

/-- P-224 as the code has it. `[k]G` for the signature and the public key is a
call of `vg_p224_mul_base` (`Cfg.mulBase`). -/
def p224 : Cfg where
  n := 4
  C := Spec.P224.curve
  comb := some ⟨7, Impl.P224.p224Comb7, Impl.P224.p224Comb7Start, "VG_P224_COMB", false, false⟩
  fastN := true
  mulBase := some Impl.Weierstrass.MulBase.p224
  inverse := some Impl.Weierstrass.Inverse.p224
  checkPoint := some Impl.Weierstrass.CheckPoint.p224

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

end VG.Impl.Ecdsa.X86_64
