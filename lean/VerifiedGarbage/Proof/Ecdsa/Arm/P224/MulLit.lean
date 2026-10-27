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
# `vg_p224_mul` on 32-bit ARM: the code as a literal

The ladder's copies and selections are unrolled, so the kernel would build
the instructions again in every check that evaluates the code (constant
time, properties of every instruction): the literal of the code
(`materialize_code`, `Proof/Framework/Lit.lean`) is checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.Arm.mulP224

/-- `vg_p224_mul`'s code has no frame, which its calls need. -/
theorem Impl.Ecdsa.Arm.mulP224_noFrames : Impl.Ecdsa.Arm.p224.mulFn.noFrames = true := by
  show Impl.Ecdsa.Arm.mulP224.noFrames = true; lit_decide

end VG
