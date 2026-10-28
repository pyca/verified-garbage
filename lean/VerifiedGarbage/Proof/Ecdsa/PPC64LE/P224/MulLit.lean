module

public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_p224_mul` on PPC64LE: the code as a literal

`vg_p224_mul` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`),
which its constant time, `spSafe` and the absence of frames its calls need
evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.PPC64LE.mulP224

/-- `vg_p224_mul`'s code has no frame, which its calls need. -/
theorem Impl.Ecdsa.PPC64LE.mulP224_noFrames : Impl.Ecdsa.PPC64LE.p224.mulFn.noFrames = true := by
  show Impl.Ecdsa.PPC64LE.mulP224.noFrames = true; lit_decide

end VG
