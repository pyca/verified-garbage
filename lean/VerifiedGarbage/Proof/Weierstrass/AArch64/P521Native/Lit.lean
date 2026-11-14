module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Shared literals for native P-521 code used by several ABI and timing checks. -/

@[expose] public section
namespace VG

materialize_code Impl.Mont.AArch64.P521Field.mulFn
materialize_code Impl.Mont.AArch64.P521Field.square
materialize_code Impl.Mont.AArch64.P521Field.doubleFn
materialize_code Impl.Mont.AArch64.P521Field.mixedFn
materialize_code Impl.Weierstrass.AArch64.P521Native.validateAndPrepare
materialize_code Impl.Weierstrass.AArch64.P521Native.callInvModP

end VG
