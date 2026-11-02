module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdsa_p384_sign` on RISC-V: the code as a literal

`vg_ecdsa_p384_sign` as a literal (`materialize_code`), whose calls of
`vg_p384_mul` and of the functions modulo `p` and `n` refer to theirs, which
its constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.Sign.signP384

/-- `vg_ecdsa_p384_sign`'s code has no frame, which its callers' calls need. -/
theorem Impl.Ecdsa.RISCV64.Sign.signP384_noFrames : Impl.Ecdsa.RISCV64.Sign.signP384.noFrames = true := by
  lit_decide

end VG
