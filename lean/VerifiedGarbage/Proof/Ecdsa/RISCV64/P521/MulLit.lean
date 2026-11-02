module

public import VerifiedGarbage.Impl.Ecdsa.P521.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P521.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_p521_mul` on RISC-V: the code as a literal

`vg_p521_mul` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`),
whose calls of the field's functions refer to theirs, which its constant
time and the absence of frames its callers' calls need evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.mulP521

/-- `vg_p521_mul`'s code has no frame, which its callers' calls need. -/
theorem Impl.Ecdsa.RISCV64.mulP521_noFrames : Impl.Ecdsa.RISCV64.mulP521.noFrames = true := by lit_decide

end VG
