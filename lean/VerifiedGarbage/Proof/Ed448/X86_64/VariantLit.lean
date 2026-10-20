module

public import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.X448.X86_64.Lit
public import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

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
