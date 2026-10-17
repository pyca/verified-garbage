module

public import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit

/-! Literal code for the ADX scalar multiplication and verification equation. -/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86_64.scalarBaseAdx
materialize_code Impl.Ed448.X86_64.verifyEquationAdx

end VG

namespace VG.Proof.Ed448.X86_64

theorem scalarBaseAdx_inlineOk : Impl.Ed448.X86_64.scalarBaseAdx.InlineOk = true := by lit_decide
theorem verifyEquationAdx_inlineOk : Impl.Ed448.X86_64.verifyEquationAdx.InlineOk = true := by
  lit_decide

end VG.Proof.Ed448.X86_64
