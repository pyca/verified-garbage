module

public import VerifiedGarbage.Impl.Ecdh.P192.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.CheckLit
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.MulLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdh.P192.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.CheckLit
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.MulLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ecdh_p192` and `vg_ec_p192_public_key` on RISC-V: the code as literals

`vg_ecdh_p192` and `vg_ec_p192_public_key` as literals (`materialize_code`),
whose calls of `vg_p192_check_point` and `vg_p192_mul`
refer to theirs, which their constant time evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdh.RISCV64.ecdhP192

materialize_code Impl.Ecdh.RISCV64.publicKeyP192

end VG
