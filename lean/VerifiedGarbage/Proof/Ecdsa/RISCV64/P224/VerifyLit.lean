module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P224
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.CheckLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.P224
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.CheckLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdsa_p224_verify` on RISC-V: the code as a literal

`vg_ecdsa_p224_verify` as a literal (`materialize_code`), whose calls of
`vg_p224_check_point`, `vg_p224_mul`, `vg_p224_mul_g` and the functions
modulo `p` and `n` refer to theirs, which its constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.P224.verifyP224

end VG
