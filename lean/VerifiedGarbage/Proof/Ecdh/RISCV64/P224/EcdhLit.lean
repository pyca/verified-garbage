module

public import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.CheckLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.CheckLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdh_p224` and `vg_ec_p224_public_key` on RISC-V: the code as literals

`vg_ecdh_p224` and `vg_ec_p224_public_key` as literals (`materialize_code`),
whose calls of `vg_p224_check_point`, `vg_p224_mul` and `vg_p224_mul_g`
refer to theirs, which their constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdh.RISCV64.ecdhP224

materialize_code Impl.Ecdh.RISCV64.publicKeyP224

end VG
