module

public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_p384_check_point` on RISC-V: the code as a literal

`vg_p384_check_point` as a literal (`materialize_code`), whose calls of the
field's functions refer to theirs, which its constant time and the absence
of frames its callers' calls need evaluate.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG

materialize_code Impl.Ecdh.RISCV64.checkP384

/-- `vg_p384_check_point`'s code has no frame, which its callers' calls need. -/
theorem Impl.Ecdh.RISCV64.checkP384_noFrames : Impl.Ecdh.RISCV64.checkP384.noFrames = true := by lit_decide

end VG
