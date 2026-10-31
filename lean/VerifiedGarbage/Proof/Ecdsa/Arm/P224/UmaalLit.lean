module

public import VerifiedGarbage.Impl.Ecdsa.P224.Arm
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.P224.Arm
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# `vg_p224_mul_umaal` on 32-bit ARM: the code as a literal

As `MulLit.lean` for `vg_p224_mul`: the literal of the code
(`materialize_code`, `Proof/Framework/Lit.lean`), checked once here.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.Arm.mulP224U

/-- `vg_p224_mul_umaal`'s code has no frame, which its calls need. -/
theorem Impl.Ecdsa.Arm.mulP224U_noFrames : (Impl.Ecdsa.Arm.p224With true).mulFn.noFrames = true := by
  show Impl.Ecdsa.Arm.mulP224U.noFrames = true; lit_decide

end VG
