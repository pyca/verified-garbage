module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.CombU
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.CombU
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_p521_mul_g` on RISC-V: the code as a literal

`vg_p521_mul_g` as a literal (`materialize_code`), whose calls of the
field's functions refer to theirs, which its constant time and the absence
of frames its callers' calls need evaluate.
-/

@[expose] public section

namespace VG

-- The entry's selection is appends nested to the left (`CombU.select`,
-- `scanWord`, `groups` and `tree`): flattened, the kernel checks it in less time.
materialize_flat_code Impl.Ecdsa.RISCV64.CombU.mulGP521

/-- `vg_p521_mul_g`'s code has no frame, which its callers' calls need. -/
theorem Impl.Ecdsa.RISCV64.CombU.mulGP521_noFrames : Impl.Ecdsa.RISCV64.CombU.mulGP521.noFrames = true := by
  lit_decide

end VG
