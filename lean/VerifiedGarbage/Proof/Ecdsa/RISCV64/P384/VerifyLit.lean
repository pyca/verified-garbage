module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.CheckLit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Lit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.CombLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.CheckLit
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Lit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdsa_p384_verify` on RISC-V: the code as a literal

`vg_ecdsa_p384_verify` as a literal (`materialize_code`), whose calls of
`vg_p384_check_point`, `vg_p384_mul`, `vg_p384_mul_g` and the functions
modulo `p` and `n` refer to theirs, which its constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.VerifyComb.verifyP384

end VG
